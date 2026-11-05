#include <cstdint>
#include <cstring>
#include <cstdlib>
#include <cstdio>
#include <cmath>
#include <algorithm>
#include <chrono>
#include <emscripten/emscripten.h>

// ============================================================================
// STOCKFISH-STYLE QUORIDOR ENGINE (C++17 / WebAssembly)
// PVS + Zobrist TT + Killer/History + Shortest-Path DAG Bottleneck Analysis
// Modes: 0 = Duel (9x9), 1 = Race (9x13), 2 = Quad (11x11, 4 players)
// ============================================================================

enum MoveType : uint8_t { MOVE_STEP = 0, MOVE_WALL = 1 };
enum TTFlag   : uint8_t { TT_NONE = 0, TT_EXACT = 1, TT_LOWER = 2, TT_UPPER = 3 };

struct Move {
    uint16_t code; // bit 0: type, bit 1: orient, bits 2..5: r, bits 6..9: c
    int32_t  orderScore;
};

static inline uint16_t packMove(int type, int r, int c, int o) {
    return (uint16_t)((type & 1) | ((o & 1) << 1) | ((r & 15) << 2) | ((c & 15) << 6));
}

struct TTEntry {
    uint64_t key;
    int32_t  score;
    uint16_t bestMove;
    int8_t   depth;
    uint8_t  flag;
};

static constexpr int TT_BITS = 18;
static constexpr int TT_SIZE = 1 << TT_BITS; // 262,144 entries
static constexpr int TT_MASK = TT_SIZE - 1;
static TTEntry TT[TT_SIZE];

// Zobrist tables
static uint64_t Z_PAWN[4][169];
static uint64_t Z_HWALL[169];
static uint64_t Z_VWALL[169];
static uint64_t Z_WALLS_LEFT[4][20];
static uint64_t Z_TURN[4];
static bool zobristInitialized = false;

static uint64_t splitmix64(uint64_t& x) {
    uint64_t z = (x += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}

static void initTables() {
    if (zobristInitialized) return;
    uint64_t seed = 0x7A4F91B3C5E82D19ULL;
    for (int p = 0; p < 4; p++) {
        Z_TURN[p] = splitmix64(seed);
        for (int s = 0; s < 169; s++) Z_PAWN[p][s] = splitmix64(seed);
        for (int w = 0; w < 20; w++)  Z_WALLS_LEFT[p][w] = splitmix64(seed);
    }
    for (int s = 0; s < 169; s++) {
        Z_HWALL[s] = splitmix64(seed);
        Z_VWALL[s] = splitmix64(seed);
    }
    zobristInitialized = true;
}

// Global Board State
static int B_ROWS = 9;
static int B_COLS = 9;
static int W_COLS = 8;
static int GAME_MODE = 0; // 0: Duel, 1: Race, 2: Quad

static uint8_t hWalls[169];
static uint8_t vWalls[169];

struct PlayerState {
    int r, c, walls;
    bool active;
};
static PlayerState P[4]; // P[0] = Me, P[1] = Opp (or Left/Top/Right in Quad)
static uint64_t hashKey = 0;

static uint16_t killerMoves[32][2];
static int32_t  historyTable[2][1024];

static int64_t  deadlineMs = 0;
static bool     aborted = false;
static uint32_t totalNodes = 0;
static int      completedDepth = 0;

// Non-linear wall value table (having 0 walls is a massive tactical liability)
static const int32_t WALL_VAL[16] = {
    0, 310, 560, 770, 950, 1110, 1255, 1390, 1515, 1630, 1740, 1845, 1945, 2040, 2130, 2215
};

static inline int64_t nowMs() {
    return std::chrono::duration_cast<std::chrono::milliseconds>(
        std::chrono::steady_clock::now().time_since_epoch()
    ).count();
}

static inline bool canUp(int r, int c) {
    if (r <= 0) return false;
    int base = (r - 1) * W_COLS;
    return (c >= W_COLS || !hWalls[base + c]) && (c <= 0 || !hWalls[base + c - 1]);
}
static inline bool canDown(int r, int c) {
    if (r >= B_ROWS - 1) return false;
    int base = r * W_COLS;
    return (c >= W_COLS || !hWalls[base + c]) && (c <= 0 || !hWalls[base + c - 1]);
}
static inline bool canLeft(int r, int c) {
    if (c <= 0) return false;
    int col = c - 1;
    return (r >= B_ROWS - 1 || !vWalls[r * W_COLS + col]) && (r <= 0 || !vWalls[(r - 1) * W_COLS + col]);
}
static inline bool canRight(int r, int c) {
    if (c >= W_COLS) return false;
    return (r >= B_ROWS - 1 || !vWalls[r * W_COLS + c]) && (r <= 0 || !vWalls[(r - 1) * W_COLS + c]);
}

static inline bool canStepDir(int r, int c, int dir) {
    if (dir == 0) return canUp(r, c);
    if (dir == 1) return canDown(r, c);
    if (dir == 2) return canLeft(r, c);
    return canRight(r, c);
}

static const int DR[4] = {-1, 1, 0, 0};
static const int DC[4] = {0, 0, -1, 1};

static inline bool wallGeometryOk(int r, int c, int o) {
    int maxR = B_ROWS - 2;
    int maxC = B_COLS - 2;
    if (r < 0 || r > maxR || c < 0 || c > maxC) return false;
    int idx = r * W_COLS + c;
    if (o == 0) {
        if (hWalls[idx] || vWalls[idx]) return false;
        if ((c > 0 && hWalls[idx - 1]) || (c < maxC && hWalls[idx + 1])) return false;
        return true;
    } else {
        if (vWalls[idx] || hWalls[idx]) return false;
        if ((r > 0 && vWalls[idx - W_COLS]) || (r < maxR && vWalls[idx + W_COLS])) return false;
        return true;
    }
}

// Fast BFS buffers
static int16_t bfsQueue[256];

static void computeGoalDistMap(int goalRow, int8_t* outDist) {
    int total = B_ROWS * B_COLS;
    memset(outDist, -1, total);
    int head = 0, tail = 0;

    if (GAME_MODE == 2) {
        int cIdx = 5 * 11 + 5;
        outDist[cIdx] = 0;
        bfsQueue[tail++] = cIdx;
    } else {
        int base = goalRow * B_COLS;
        for (int c = 0; c < B_COLS; c++) {
            outDist[base + c] = 0;
            bfsQueue[tail++] = base + c;
        }
    }

    while (head < tail) {
        int idx = bfsQueue[head++];
        int r = idx / B_COLS;
        int c = idx - r * B_COLS;
        int8_t nd = outDist[idx] + 1;

        if (canUp(r, c) && outDist[idx - B_COLS] == -1) {
            outDist[idx - B_COLS] = nd; bfsQueue[tail++] = idx - B_COLS;
        }
        if (canDown(r, c) && outDist[idx + B_COLS] == -1) {
            outDist[idx + B_COLS] = nd; bfsQueue[tail++] = idx + B_COLS;
        }
        if (canLeft(r, c) && outDist[idx - 1] == -1) {
            outDist[idx - 1] = nd; bfsQueue[tail++] = idx - 1;
        }
        if (canRight(r, c) && outDist[idx + 1] == -1) {
            outDist[idx + 1] = nd; bfsQueue[tail++] = idx + 1;
        }
    }
}

static inline int countExits(int r, int c, const int8_t* distMap) {
    int idx = r * B_COLS + c;
    int d = distMap[idx];
    if (d <= 0) return 0;
    int target = d - 1;
    int ex = 0;
    if (canUp(r, c)    && distMap[idx - B_COLS] == target) ex++;
    if (canDown(r, c)  && distMap[idx + B_COLS] == target) ex++;
    if (canLeft(r, c)  && distMap[idx - 1] == target) ex++;
    if (canRight(r, c) && distMap[idx + 1] == target) ex++;
    return ex;
}

static inline bool isOccupiedOther(int r, int c, int ignoreP) {
    int count = (GAME_MODE == 2) ? 4 : 2;
    for (int i = 0; i < count; i++) {
        if (i != ignoreP && P[i].active && P[i].r == r && P[i].c == c) return true;
    }
    return false;
}

static int getPawnSteps(int pIdx, int* outSteps) {
    int r = P[pIdx].r, c = P[pIdx].c;
    int cnt = 0;
    for (int d = 0; d < 4; d++) {
        if (!canStepDir(r, c, d)) continue;
        int nr = r + DR[d], nc = c + DC[d];
        if (isOccupiedOther(nr, nc, pIdx)) {
            int jr = nr + DR[d], jc = nc + DC[d];
            if (jr >= 0 && jr < B_ROWS && jc >= 0 && jc < B_COLS &&
                canStepDir(nr, nc, d) && !isOccupiedOther(jr, jc, pIdx)) {
                outSteps[cnt++] = jr * B_COLS + jc;
            } else {
                if (d < 2) {
                    if (canLeft(nr, nc)  && !isOccupiedOther(nr, nc - 1, pIdx)) outSteps[cnt++] = nr * B_COLS + (nc - 1);
                    if (canRight(nr, nc) && !isOccupiedOther(nr, nc + 1, pIdx)) outSteps[cnt++] = nr * B_COLS + (nc + 1);
                } else {
                    if (canUp(nr, nc)    && !isOccupiedOther(nr - 1, nc, pIdx)) outSteps[cnt++] = (nr - 1) * B_COLS + nc;
                    if (canDown(nr, nc)  && !isOccupiedOther(nr + 1, nc, pIdx)) outSteps[cnt++] = (nr + 1) * B_COLS + nc;
                }
            }
        } else {
            outSteps[cnt++] = nr * B_COLS + nc;
        }
    }
    return cnt;
}

// ============================================================================
// EVALUATION (ALWAYS FROM MOVER'S PERSPECTIVE FOR NEGAMAX)
// ============================================================================
static int32_t evaluate2P(int sideToMove) {
    int myGoal  = 0;
    int oppGoal = (GAME_MODE == 1) ? 0 : (B_ROWS - 1);

    if (P[0].r == myGoal)  return (sideToMove == 0) ?  10000000 : -10000000;
    if (P[1].r == oppGoal) return (sideToMove == 0) ? -10000000 :  10000000;

    int8_t meMap[169], oppMap[169];
    computeGoalDistMap(myGoal, meMap);
    if (GAME_MODE == 1) {
        memcpy(oppMap, meMap, B_ROWS * B_COLS);
    } else {
        computeGoalDistMap(oppGoal, oppMap);
    }

    int myD  = meMap[P[0].r * B_COLS + P[0].c];
    int oppD = oppMap[P[1].r * B_COLS + P[1].c];
    if (myD < 0)  return (sideToMove == 0) ? -10000000 :  10000000;
    if (oppD < 0) return (sideToMove == 0) ?  10000000 : -10000000;

    // Effective race distance including half-tempo for having the right to move
    // 1 full step = 1600 points; right to move = +800 points
    int32_t scoreForMe = (oppD - myD) * 1600 + (sideToMove == 0 ? 800 : -800);

    // Non-linear wall inventory value
    int mw = std::min(15, std::max(0, P[0].walls));
    int ow = std::min(15, std::max(0, P[1].walls));
    scoreForMe += (WALL_VAL[mw] - WALL_VAL[ow]);

    // Severe penalty for running completely out of walls while opponent still has walls
    if (mw == 0 && ow > 0) scoreForMe -= 1400;
    if (ow == 0 && mw > 0) scoreForMe += 1400;

    // Route flexibility (optimal exits)
    int myExits  = countExits(P[0].r, P[0].c, meMap);
    int oppExits = countExits(P[1].r, P[1].c, oppMap);
    scoreForMe += (myExits - oppExits) * 150;
    if (oppExits == 1 && mw > 0) scoreForMe += 350;
    if (myExits == 1  && ow > 0) scoreForMe -= 350;

    // Direct jump threat when pawns are adjacent in Duel
    if (GAME_MODE == 0 && (abs(P[0].r - P[1].r) + abs(P[0].c - P[1].c) == 1)) {
        int steps[8];
        if (sideToMove == 0) {
            int n = getPawnSteps(0, steps);
            for (int i = 0; i < n; i++) {
                if (meMap[steps[i]] <= myD - 2) { scoreForMe += 950; break; }
            }
        } else {
            int n = getPawnSteps(1, steps);
            for (int i = 0; i < n; i++) {
                if (oppMap[steps[i]] <= oppD - 2) { scoreForMe -= 950; break; }
            }
        }
    }

    // Center control / separation
    if (GAME_MODE == 1) {
        if (myD <= oppD) scoreForMe += abs(P[0].c - P[1].c) * 22;
    } else {
        int myCenter  = 4 - abs(P[0].c - 4);
        int oppCenter = 4 - abs(P[1].c - 4);
        scoreForMe += (myCenter - oppCenter) * 18;
    }

    // Endgame urgency
    if (myD <= 3 || oppD <= 3) {
        scoreForMe += (oppD - myD) * 550;
    }

    return (sideToMove == 0) ? scoreForMe : -scoreForMe;
}

static int generateMoves2P(int side, Move* outMoves, uint16_t ttBest, int ply, bool isRoot) {
    int enemy = 1 - side;
    int pR = P[side].r,  pC = P[side].c,  pW = P[side].walls;
    int eR = P[enemy].r, eC = P[enemy].c;
    int pGoal = (side == 0 || GAME_MODE == 1) ? 0 : (B_ROWS - 1);
    int eGoal = (enemy == 0 || GAME_MODE == 1) ? 0 : (B_ROWS - 1);

    int8_t pMap[169], eMap[169];
    computeGoalDistMap(pGoal, pMap);
    if (pGoal == eGoal) memcpy(eMap, pMap, B_ROWS * B_COLS);
    else computeGoalDistMap(eGoal, eMap);

    int curP = pMap[pR * B_COLS + pC];
    int curE = eMap[eR * B_COLS + eC];
    int curEExits = countExits(eR, eC, eMap);

    int count = 0;
    int steps[8];
    int nSteps = getPawnSteps(side, steps);

    for (int i = 0; i < nSteps; i++) {
        int sr = steps[i] / B_COLS;
        int sc = steps[i] % B_COLS;
        uint16_t code = packMove(MOVE_STEP, sr, sc, 0);
        if (sr == pGoal) {
            outMoves[0] = {code, 100000000};
            return 1;
        }
        int newD = pMap[steps[i]];
        int gain = curP - newD;
        int32_t prio = gain * 12000 + historyTable[side][code & 1023];
        if (code == ttBest) prio += 50000000;
        if (gain >= 2) prio += 7000;
        outMoves[count++] = {code, prio};
    }

    if (pW <= 0) {
        std::sort(outMoves, outMoves + count, [](const Move& a, const Move& b) {
            return a.orderScore > b.orderScore;
        });
        return count;
    }

    Move wallList[256];
    int wCount = 0;
    int maxR = B_ROWS - 2;
    int maxC = B_COLS - 2;

    for (int r = 0; r <= maxR; r++) {
        for (int c = 0; c <= maxC; c++) {
            int idxTL = r * B_COLS + c;
            int dTL = eMap[idxTL];
            int dTR = eMap[idxTL + 1];
            int dBL = eMap[idxTL + B_COLS];
            int dBR = eMap[idxTL + B_COLS + 1];

            bool nearE = (abs(r - eR) <= 3 && abs(c - eC) <= 3);
            bool nearP = (abs(r - pR) <= 2 && abs(c - pC) <= 2);

            for (int o = 0; o < 2; o++) {
                if (!wallGeometryOk(r, c, o)) continue;

                bool cutsShortest = false;
                if (o == 0) {
                    cutsShortest = (abs(dTL - dBL) == 1 && std::min(dTL, dBL) < curE) ||
                                   (abs(dTR - dBR) == 1 && std::min(dTR, dBR) < curE);
                } else {
                    cutsShortest = (abs(dTL - dTR) == 1 && std::min(dTL, dTR) < curE) ||
                                   (abs(dBL - dBR) == 1 && std::min(dBL, dBR) < curE);
                }

                if (!isRoot && !cutsShortest && !nearE && !nearP) continue;

                int wIdx = r * W_COLS + c;
                if (o == 0) hWalls[wIdx] = 1; else vWalls[wIdx] = 1;

                int8_t nPMap[169], nEMap[169];
                computeGoalDistMap(pGoal, nPMap);
                if (pGoal == eGoal) memcpy(nEMap, nPMap, B_ROWS * B_COLS);
                else computeGoalDistMap(eGoal, nEMap);

                if (o == 0) hWalls[wIdx] = 0; else vWalls[wIdx] = 0;

                int newP = nPMap[pR * B_COLS + pC];
                int newE = nEMap[eR * B_COLS + eC];
                if (newP < 0 || newE < 0) continue;

                int eGain = newE - curE;
                int pLoss = newP - curP;
                int net   = eGain - pLoss;
                int newEExits = countExits(eR, eC, nEMap);
                int exitDrop  = curEExits - newEExits;

                if (!isRoot && net < 0 && exitDrop <= 0) continue;
                if (!isRoot && net == 0 && exitDrop <= 0 && !nearE) continue;

                uint16_t code = packMove(MOVE_WALL, r, c, o);
                int32_t prio = net * 7500 + eGain * 2500 + exitDrop * 2100 + historyTable[side][code & 1023];
                if (code == ttBest) prio += 50000000;
                if (killerMoves[ply][0] == code || killerMoves[ply][1] == code) prio += 5500;
                if (eGain >= 2 && pLoss == 0) prio += 4500;

                wallList[wCount++] = {code, prio};
            }
        }
    }

    std::sort(wallList, wallList + wCount, [](const Move& a, const Move& b) {
        return a.orderScore > b.orderScore;
    });

    int limit = isRoot ? 44 : (ply <= 2 ? 20 : 14);
    int take = std::min(limit, wCount);
    for (int i = 0; i < take; i++) {
        outMoves[count++] = wallList[i];
    }

    std::sort(outMoves, outMoves + count, [](const Move& a, const Move& b) {
        return a.orderScore > b.orderScore;
    });
    return count;
}

static void doMove2P(int side, uint16_t code, int& savedR, int& savedC) {
    int type = code & 1;
    int o    = (code >> 1) & 1;
    int r    = (code >> 2) & 15;
    int c    = (code >> 6) & 15;

    hashKey ^= Z_TURN[side] ^ Z_TURN[1 - side];
    if (type == MOVE_STEP) {
        savedR = P[side].r;
        savedC = P[side].c;
        hashKey ^= Z_PAWN[side][savedR * B_COLS + savedC];
        P[side].r = r;
        P[side].c = c;
        hashKey ^= Z_PAWN[side][r * B_COLS + c];
    } else {
        int idx = r * W_COLS + c;
        if (o == 0) { hWalls[idx] = 1; hashKey ^= Z_HWALL[idx]; }
        else        { vWalls[idx] = 1; hashKey ^= Z_VWALL[idx]; }
        hashKey ^= Z_WALLS_LEFT[side][P[side].walls];
        P[side].walls--;
        hashKey ^= Z_WALLS_LEFT[side][P[side].walls];
    }
}

static void undoMove2P(int side, uint16_t code, int savedR, int savedC) {
    int type = code & 1;
    int o    = (code >> 1) & 1;
    int r    = (code >> 2) & 15;
    int c    = (code >> 6) & 15;

    hashKey ^= Z_TURN[1 - side] ^ Z_TURN[side];
    if (type == MOVE_STEP) {
        hashKey ^= Z_PAWN[side][r * B_COLS + c];
        P[side].r = savedR;
        P[side].c = savedC;
        hashKey ^= Z_PAWN[side][savedR * B_COLS + savedC];
    } else {
        int idx = r * W_COLS + c;
        if (o == 0) { hWalls[idx] = 0; hashKey ^= Z_HWALL[idx]; }
        else        { vWalls[idx] = 0; hashKey ^= Z_VWALL[idx]; }
        hashKey ^= Z_WALLS_LEFT[side][P[side].walls];
        P[side].walls++;
        hashKey ^= Z_WALLS_LEFT[side][P[side].walls];
    }
}

static int32_t negamaxPVS(int depth, int ply, int32_t alpha, int32_t beta, int side) {
    if ((++totalNodes & 127) == 0 && nowMs() >= deadlineMs) {
        aborted = true;
        return 0;
    }

    int myGoal  = 0;
    int oppGoal = (GAME_MODE == 1) ? 0 : (B_ROWS - 1);
    if (P[0].r == myGoal)  return (side == 0) ? (10000000 - ply) : -(10000000 - ply);
    if (P[1].r == oppGoal) return (side == 0) ? -(10000000 - ply) : (10000000 - ply);

    if (depth <= 0) {
        return evaluate2P(side);
    }

    int32_t alphaOrig = alpha;
    TTEntry& tte = TT[hashKey & TT_MASK];
    uint16_t ttBest = 0;

    if (tte.flag != TT_NONE && tte.key == hashKey) {
        ttBest = tte.bestMove;
        if (tte.depth >= depth && ply > 0) {
            if (tte.flag == TT_EXACT) return tte.score;
            if (tte.flag == TT_LOWER && tte.score > alpha) alpha = tte.score;
            else if (tte.flag == TT_UPPER && tte.score < beta) beta = tte.score;
            if (alpha >= beta) return tte.score;
        }
    }

    Move moves[128];
    int nMoves = generateMoves2P(side, moves, ttBest, ply, ply == 0);
    if (nMoves == 0) return evaluate2P(side);

    int32_t bestScore = -100000000;
    uint16_t bestMove = moves[0].code;

    for (int i = 0; i < nMoves; i++) {
        uint16_t code = moves[i].code;
        int sr = 0, sc = 0;
        doMove2P(side, code, sr, sc);

        int32_t score;
        if (i == 0) {
            score = -negamaxPVS(depth - 1, ply + 1, -beta, -alpha, 1 - side);
        } else {
            int reduction = (depth >= 4 && i >= 6 && (code & 1) == MOVE_WALL) ? 1 : 0;
            score = -negamaxPVS(depth - 1 - reduction, ply + 1, -alpha - 1, -alpha, 1 - side);
            if (!aborted && score > alpha && score < beta) {
                score = -negamaxPVS(depth - 1, ply + 1, -beta, -alpha, 1 - side);
            }
        }

        undoMove2P(side, code, sr, sc);
        if (aborted) return 0;

        if (score > bestScore) {
            bestScore = score;
            bestMove  = code;
            if (score > alpha) {
                alpha = score;
                if (alpha >= beta) {
                    if (killerMoves[ply][0] != code) {
                        killerMoves[ply][1] = killerMoves[ply][0];
                        killerMoves[ply][0] = code;
                    }
                    historyTable[side][code & 1023] = std::min(500000, historyTable[side][code & 1023] + depth * depth * 80);
                    break;
                }
            }
        }
    }

    uint8_t flag = TT_EXACT;
    if (bestScore <= alphaOrig) flag = TT_UPPER;
    else if (bestScore >= beta) flag = TT_LOWER;

    tte.key      = hashKey;
    tte.score    = bestScore;
    tte.bestMove = bestMove;
    tte.depth    = (int8_t)depth;
    tte.flag     = flag;

    return bestScore;
}

extern "C" {

EMSCRIPTEN_KEEPALIVE
void initEngine() {
    initTables();
    memset(TT, 0, sizeof(TT));
}

EMSCRIPTEN_KEEPALIVE
int search(int mode, int rows, int cols,
           int mR, int mC, int mW,
           int oR, int oC, int oW,
           const char* wallListStr,
           int timeMs, int maxDepth) {
    initTables();

    GAME_MODE = mode;
    B_ROWS = rows;
    B_COLS = cols;
    W_COLS = cols - 1;

    P[0] = {mR, mC, mW, true};
    P[1] = {oR, oC, oW, true};
    P[2] = {0, 0, 0, false};
    P[3] = {0, 0, 0, false};

    memset(hWalls, 0, sizeof(hWalls));
    memset(vWalls, 0, sizeof(vWalls));
    memset(killerMoves, 0, sizeof(killerMoves));
    memset(historyTable, 0, sizeof(historyTable));

    hashKey = Z_TURN[0] ^
              Z_PAWN[0][mR * B_COLS + mC] ^ Z_WALLS_LEFT[0][std::min(19, mW)] ^
              Z_PAWN[1][oR * B_COLS + oC] ^ Z_WALLS_LEFT[1][std::min(19, oW)];

    if (wallListStr && wallListStr[0] != '\0') {
        char buf[4096];
        strncpy(buf, wallListStr, sizeof(buf) - 1);
        buf[sizeof(buf) - 1] = '\0';
        char* tok = strtok(buf, ";");
        while (tok) {
            int wr, wc; char wo;
            if (sscanf(tok, "%d,%d,%c", &wr, &wc, &wo) == 3) {
                int idx = wr * W_COLS + wc;
                if (wo == 'h') { hWalls[idx] = 1; hashKey ^= Z_HWALL[idx]; }
                else           { vWalls[idx] = 1; hashKey ^= Z_VWALL[idx]; }
            }
            tok = strtok(nullptr, ";");
        }
    }

    totalNodes = 0;
    aborted = false;
    completedDepth = 0;
    deadlineMs = nowMs() + std::max(300, std::min(5000, timeMs));

    Move rootMoves[128];
    int nRoot = generateMoves2P(0, rootMoves, 0, 0, true);
    if (nRoot == 0) return 0;
    if (nRoot == 1) return rootMoves[0].code;

    uint16_t bestCode = rootMoves[0].code;
    int limitDepth = std::min(20, std::max(2, maxDepth));

    for (int d = 1; d <= limitDepth; d++) {
        if (nowMs() >= deadlineMs) break;
        aborted = false;
        int32_t score = negamaxPVS(d, 0, -100000000, 100000000, 0);
        if (!aborted) {
            TTEntry& tte = TT[hashKey & TT_MASK];
            if (tte.key == hashKey && tte.bestMove != 0) {
                bestCode = tte.bestMove;
            }
            completedDepth = d;
            if (score >= 9000000) break;
        } else {
            break;
        }
    }

    return (int)bestCode;
}

}
