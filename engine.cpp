#include <iostream>
#include <vector>
#include <cstdint>
#include <algorithm>
#include <chrono>
#include <cstring>
#include <cmath>
#include <emscripten/emscripten.h>

using namespace std;

// ============================================================================
// STOCKFISH 16/17 ARCHITECTURE QUORIDOR ENGINE (C++ / WASM)
// - Zero-GC Flat Bit/Array Graph Representation
// - 64-Bit Zobrist Hashing with 2-Way Cluster Transposition Table
//   (Slot 0: Depth-Preferred, Slot 1: Always-Replace)
// - Exact Path Multiplicity (DAG route counting) & Cut Disjunction
// - Dynamic Convex Tempo-Material Model (Zero artificial opening bans)
// - Quiescence Search (Tactical Pawn Contact & Forcing Wall Resolution)
// - Iterative Deepening + Aspiration Windows + PVS + Dynamic LMR
// - Killer Moves (2/ply) + History Heuristic + Countermove Heuristic
// - Specialized Evaluators: Duel (9x9), Race (9x13), Quad 4-Player (11x11)
// ============================================================================

enum MoveType : uint8_t { STEP = 0, WALL = 1 };

struct Move {
    uint8_t type; // 0 = step, 1 = wall
    uint8_t r, c, o; // o: 0 = h, 1 = v
    int32_t orderScore;
};

static inline uint16_t packMove16(uint8_t type, uint8_t r, uint8_t c, uint8_t o) {
    return (uint16_t)((type & 1) | ((o & 1) << 1) | ((r & 15) << 2) | ((c & 15) << 6));
}

static inline void unpackMove16(uint16_t code, uint8_t& type, uint8_t& r, uint8_t& c, uint8_t& o) {
    type = code & 1;
    o = (code >> 1) & 1;
    r = (code >> 2) & 15;
    c = (code >> 6) & 15;
}

enum TTFlag : uint8_t { TT_NONE = 0, TT_EXACT = 1, TT_LOWER = 2, TT_UPPER = 3 };

struct TTEntry {
    uint64_t key;
    int32_t score;
    int8_t depth;
    uint8_t flag;
    uint16_t bestMove;
};

struct TTCluster {
    TTEntry depthPreferred;
    TTEntry alwaysReplace;
};

static const int TT_CLUSTERS = 1 << 19; // 524,288 clusters = 1,048,576 entries
static const int TT_MASK = TT_CLUSTERS - 1;
static TTCluster TT[TT_CLUSTERS];

struct PathMetrics {
    int8_t dist;
    int16_t ways;   // Number of distinct shortest paths to goal
    uint8_t exits;  // Number of immediate optimal neighbor steps
};

struct DistCacheEntry {
    uint64_t wallKey;
    PathMetrics me[144];
    PathMetrics opp[144];
    bool valid;
};

static const int DC_SIZE = 1 << 15; // 32,768 cached wall topologies
static const int DC_MASK = DC_SIZE - 1;
static DistCacheEntry DistCache[DC_SIZE];

// Zobrist Keys
static uint64_t Z_ME[169];
static uint64_t Z_OPP[169];
static uint64_t Z_HWALL[169];
static uint64_t Z_VWALL[169];
static uint64_t Z_MW[20];
static uint64_t Z_OW[20];
static uint64_t Z_TURN;

// Board & State
static int B_ROWS = 9;
static int B_COLS = 9;
static int GAME_MODE = 0; // 0 = Duel 9x9, 1 = Race 9x13, 2 = Quad 11x11

static uint8_t hWalls[169];
static uint8_t vWalls[169];
static int totalWallsOnBoard = 0;

static int myR = 8, myC = 4, myWalls = 10;
static int oppR = 0, oppC = 4, oppWalls = 10;

struct QuadPlayer {
    int r, c, walls;
    bool active;
};
static QuadPlayer quadP[4];

static uint64_t wallZobrist = 0;
static uint16_t killerMoves[64][2];
static uint16_t counterMoves[2][1024];
static int32_t historyTable[2][1024];

static int64_t searchDeadline = 0;
static bool searchAborted = false;
static uint32_t nodesSearched = 0;
static int completedDepthGlobal = 0;

// Non-linear convex wall valuation table (centipawns, where 1 step = 1000).
// Spending a wall from 10->9 costs 1420 material + 1000 tempo = 2420 total.
// Therefore, a 1-step delay (+1000) is a net -1420 loss, naturally preventing
// premature wall waste without any artificial opening bans.
static const int32_t WALL_MATERIAL_TABLE[16] = {
    0,     // 0 walls
    2600,  // 1st wall (last reserve is priceless)
    4900,  // 2
    7000,  // 3
    8950,  // 4
    10780, // 5
    12510, // 6
    14160, // 7
    15740, // 8
    17260, // 9
    18680, // 10
    20050, // 11
    21380, // 12
    22670, // 13
    23920, // 14
    25140  // 15
};

static inline int64_t nowMs() {
    return chrono::duration_cast<chrono::milliseconds>(
        chrono::steady_clock::now().time_since_epoch()
    ).count();
}

static uint64_t splitmix64(uint64_t& x) {
    uint64_t z = (x += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}

static void initTables() {
    uint64_t seed = 0x517cc1b727220a95ULL;
    for (int i = 0; i < 169; i++) {
        Z_ME[i] = splitmix64(seed);
        Z_OPP[i] = splitmix64(seed);
        Z_HWALL[i] = splitmix64(seed);
        Z_VWALL[i] = splitmix64(seed);
    }
    for (int i = 0; i < 20; i++) {
        Z_MW[i] = splitmix64(seed);
        Z_OW[i] = splitmix64(seed);
    }
    Z_TURN = splitmix64(seed);
}

static inline bool canUp(int r, int c) {
    if (r <= 0) return false;
    int wC = B_COLS - 1;
    int base = (r - 1) * wC;
    return (c >= wC || hWalls[base + c] == 0) && (c <= 0 || hWalls[base + c - 1] == 0);
}

static inline bool canDown(int r, int c) {
    if (r >= B_ROWS - 1) return false;
    int wC = B_COLS - 1;
    int base = r * wC;
    return (c >= wC || hWalls[base + c] == 0) && (c <= 0 || hWalls[base + c - 1] == 0);
}

static inline bool canLeft(int r, int c) {
    if (c <= 0) return false;
    int wC = B_COLS - 1;
    return (r >= B_ROWS - 1 || vWalls[r * wC + c - 1] == 0) && (r <= 0 || vWalls[(r - 1) * wC + c - 1] == 0);
}

static inline bool canRight(int r, int c) {
    int wC = B_COLS - 1;
    if (c >= wC) return false;
    return (r >= B_ROWS - 1 || vWalls[r * wC + c] == 0) && (r <= 0 || vWalls[(r - 1) * wC + c] == 0);
}

static inline bool canStepDir(int r, int c, int dir) {
    if (dir == 0) return canUp(r, c);
    if (dir == 1) return canDown(r, c);
    if (dir == 2) return canLeft(r, c);
    return canRight(r, c);
}

static inline void placeWallInternal(int r, int c, int o) {
    int idx = r * (B_COLS - 1) + c;
    if (o == 0) {
        hWalls[idx] = 1;
        wallZobrist ^= Z_HWALL[idx];
    } else {
        vWalls[idx] = 1;
        wallZobrist ^= Z_VWALL[idx];
    }
    totalWallsOnBoard++;
}

static inline void removeWallInternal(int r, int c, int o) {
    int idx = r * (B_COLS - 1) + c;
    if (o == 0) {
        hWalls[idx] = 0;
        wallZobrist ^= Z_HWALL[idx];
    } else {
        vWalls[idx] = 0;
        wallZobrist ^= Z_VWALL[idx];
    }
    totalWallsOnBoard--;
}

static inline bool wallGeometryLegal(int r, int c, int o) {
    int maxR = B_ROWS - 2;
    int maxC = B_COLS - 2;
    if (r < 0 || r > maxR || c < 0 || c > maxC) return false;
    int stride = B_COLS - 1;
    int idx = r * stride + c;
    if (o == 0) {
        if (hWalls[idx] || vWalls[idx]) return false;
        if ((c > 0 && hWalls[idx - 1]) || (c < maxC && hWalls[idx + 1])) return false;
        return true;
    } else {
        if (vWalls[idx] || hWalls[idx]) return false;
        if ((r > 0 && vWalls[idx - stride]) || (r < maxR && vWalls[idx + stride])) return false;
        return true;
    }
}

// ============================================================================
// REVERSE WAVEFRONT BFS WITH PATH MULTIPLICITY (WAYS) & OPTIMAL EXITS
// ============================================================================
static int16_t bfsQ[256];

static void runReverseGoalBfs(int goalRow, PathMetrics* outMetrics) {
    int total = B_ROWS * B_COLS;
    for (int i = 0; i < total; i++) {
        outMetrics[i] = {-1, 0, 0};
    }

    int head = 0, tail = 0;
    int base = goalRow * B_COLS;
    for (int c = 0; c < B_COLS; c++) {
        int idx = base + c;
        outMetrics[idx].dist = 0;
        outMetrics[idx].ways = 1;
        bfsQ[tail++] = idx;
    }

    while (head < tail) {
        int idx = bfsQ[head++];
        int r = idx / B_COLS;
        int c = idx - r * B_COLS;
        int8_t nd = outMetrics[idx].dist + 1;
        int16_t curWays = outMetrics[idx].ways;

        const auto expand = [&](bool open, int ni) {
            if (!open) return;
            if (outMetrics[ni].dist == -1) {
                outMetrics[ni].dist = nd;
                outMetrics[ni].ways = curWays;
                bfsQ[tail++] = ni;
            } else if (outMetrics[ni].dist == nd) {
                int32_t sum = (int32_t)outMetrics[ni].ways + curWays;
                outMetrics[ni].ways = (int16_t)(sum > 4096 ? 4096 : sum);
            }
        };

        expand(canUp(r, c), idx - B_COLS);
        expand(canDown(r, c), idx + B_COLS);
        expand(canLeft(r, c), idx - 1);
        expand(canRight(r, c), idx + 1);
    }

    for (int idx = 0; idx < total; idx++) {
        int8_t d = outMetrics[idx].dist;
        if (d <= 0) continue;
        int r = idx / B_COLS;
        int c = idx - r * B_COLS;
        int8_t target = d - 1;
        uint8_t exits = 0;
        if (canUp(r, c) && outMetrics[idx - B_COLS].dist == target) exits++;
        if (canDown(r, c) && outMetrics[idx + B_COLS].dist == target) exits++;
        if (canLeft(r, c) && outMetrics[idx - 1].dist == target) exits++;
        if (canRight(r, c) && outMetrics[idx + 1].dist == target) exits++;
        outMetrics[idx].exits = exits;
    }
}

static void runCenterBfs11(PathMetrics* outMetrics) {
    for (int i = 0; i < 121; i++) {
        outMetrics[i] = {-1, 0, 0};
    }
    int head = 0, tail = 0;
    int centerIdx = 5 * 11 + 5;
    outMetrics[centerIdx].dist = 0;
    outMetrics[centerIdx].ways = 1;
    bfsQ[tail++] = centerIdx;

    while (head < tail) {
        int idx = bfsQ[head++];
        int r = idx / 11;
        int c = idx - r * 11;
        int8_t nd = outMetrics[idx].dist + 1;
        int16_t curWays = outMetrics[idx].ways;

        const auto expand = [&](bool open, int ni) {
            if (!open) return;
            if (outMetrics[ni].dist == -1) {
                outMetrics[ni].dist = nd;
                outMetrics[ni].ways = curWays;
                bfsQ[tail++] = ni;
            } else if (outMetrics[ni].dist == nd) {
                int32_t sum = (int32_t)outMetrics[ni].ways + curWays;
                outMetrics[ni].ways = (int16_t)(sum > 4096 ? 4096 : sum);
            }
        };

        expand(canUp(r, c), idx - 11);
        expand(canDown(r, c), idx + 11);
        expand(canLeft(r, c), idx - 1);
        expand(canRight(r, c), idx + 1);
    }

    for (int idx = 0; idx < 121; idx++) {
        int8_t d = outMetrics[idx].dist;
        if (d <= 0) continue;
        int r = idx / 11;
        int c = idx - r * 11;
        int8_t target = d - 1;
        uint8_t exits = 0;
        if (canUp(r, c) && outMetrics[idx - 11].dist == target) exits++;
        if (canDown(r, c) && outMetrics[idx + 11].dist == target) exits++;
        if (canLeft(r, c) && outMetrics[idx - 1].dist == target) exits++;
        if (canRight(r, c) && outMetrics[idx + 1].dist == target) exits++;
        outMetrics[idx].exits = exits;
    }
}

static inline const DistCacheEntry& getCachedDistMaps() {
    uint64_t key = wallZobrist ^ (uint64_t)(GAME_MODE * 0x9e3779b1);
    DistCacheEntry& entry = DistCache[key & DC_MASK];
    if (entry.valid && entry.wallKey == key) {
        return entry;
    }
    entry.wallKey = key;
    entry.valid = true;
    if (GAME_MODE == 2) {
        runCenterBfs11(entry.me);
    } else if (GAME_MODE == 1) {
        runReverseGoalBfs(0, entry.me);
        memcpy(entry.opp, entry.me, sizeof(PathMetrics) * (B_ROWS * B_COLS));
    } else {
        runReverseGoalBfs(0, entry.me);
        runReverseGoalBfs(B_ROWS - 1, entry.opp);
    }
    return entry;
}

static const int DR[4] = {-1, 1, 0, 0};
static const int DC[4] = {0, 0, -1, 1};

static int generatePawnSteps2P(int pR, int pC, int oR, int oC, int* outCells) {
    int cnt = 0;
    for (int d = 0; d < 4; d++) {
        if (!canStepDir(pR, pC, d)) continue;
        int nr = pR + DR[d], nc = pC + DC[d];
        if (nr == oR && nc == oC) {
            if (canStepDir(oR, oC, d)) {
                outCells[cnt++] = (oR + DR[d]) * B_COLS + (oC + DC[d]);
            } else {
                if (d < 2) {
                    if (canLeft(oR, oC)) outCells[cnt++] = oR * B_COLS + (oC - 1);
                    if (canRight(oR, oC)) outCells[cnt++] = oR * B_COLS + (oC + 1);
                } else {
                    if (canUp(oR, oC)) outCells[cnt++] = (oR - 1) * B_COLS + oC;
                    if (canDown(oR, oC)) outCells[cnt++] = (oR + 1) * B_COLS + oC;
                }
            }
        } else {
            outCells[cnt++] = nr * B_COLS + nc;
        }
    }
    return cnt;
}

// ============================================================================
// STOCKFISH-GRADE EVALUATION FUNCTION (DUEL 9x9 & RACE 9x13)
// ============================================================================
static const int32_t STEP_TEMPO_VALUE = 1000;

static inline int fastLog2Ways(int16_t ways) {
    if (ways <= 1) return 0;
    if (ways <= 2) return 1;
    if (ways <= 4) return 2;
    if (ways <= 8) return 3;
    if (ways <= 16) return 4;
    if (ways <= 32) return 5;
    return 6;
}

static int evaluate2P(bool sideToMoveIsMe) {
    int oppGoal = (GAME_MODE == 1) ? 0 : B_ROWS - 1;
    if (myR == 0) return 100000;
    if (oppR == oppGoal) return -100000;

    const DistCacheEntry& dc = getCachedDistMaps();
    int myIdx = myR * B_COLS + myC;
    int oppIdx = oppR * B_COLS + oppC;
    const PathMetrics& myM = dc.me[myIdx];
    const PathMetrics& oppM = dc.opp[oppIdx];

    if (myM.dist < 0) return -100000;
    if (oppM.dist < 0) return 100000;

    // 1. Exact Race Delta (1000 cp per step)
    int32_t score = (oppM.dist - myM.dist) * STEP_TEMPO_VALUE;

    // 2. Side-to-Move Initiative (0.5 step = 500 cp)
    score += (sideToMoveIsMe ? 500 : -500);

    // 3. Non-Linear Convex Wall Material Balance
    int mwClamped = min(15, max(0, myWalls));
    int owClamped = min(15, max(0, oppWalls));
    score += (WALL_MATERIAL_TABLE[mwClamped] - WALL_MATERIAL_TABLE[owClamped]);

    // 4. Path Multiplicity (Route Diversity) & Bottleneck Exits
    int myFlex = fastLog2Ways(myM.ways) * 85 + myM.exits * 145;
    int oppFlex = fastLog2Ways(oppM.ways) * 85 + oppM.exits * 145;
    score += (myFlex - oppFlex);

    // Single-exit corridor pressure when opponent has walls in hand
    if (oppM.exits == 1 && myWalls > 0) score += 310;
    if (myM.exits == 1 && oppWalls > 0) score -= 330;

    // 5. Mode-specific topological terms
    if (GAME_MODE == 1) {
        // Race 9x13: Separation Index — when ahead or tied, lateral separation prevents shared horizontal blocks
        int colSep = abs(myC - oppC);
        if (myM.dist <= oppM.dist) score += colSep * 28;
    } else {
        // Duel 9x9: Jump Tempo Opposition when pawns are adjacent or 2 cells apart
        int manhattan = abs(myR - oppR) + abs(myC - oppC);
        if (manhattan == 1) {
            int stepBuf[8];
            if (sideToMoveIsMe) {
                int n = generatePawnSteps2P(myR, myC, oppR, oppC, stepBuf);
                for (int i = 0; i < n; i++) {
                    if (dc.me[stepBuf[i]].dist <= myM.dist - 2) { score += 920; break; }
                }
            } else {
                int n = generatePawnSteps2P(oppR, oppC, myR, myC, stepBuf);
                for (int i = 0; i < n; i++) {
                    if (dc.opp[stepBuf[i]].dist <= oppM.dist - 2) { score -= 920; break; }
                }
            }
        }
        int myCenter = 4 - abs(myC - 4);
        int oppCenter = 4 - abs(oppC - 4);
        score += (myCenter - oppCenter) * 18;
    }

    // Endgame urgency scaling
    if (myM.dist <= 3 || oppM.dist <= 3) {
        score += (oppM.dist - myM.dist) * 420;
    }

    return sideToMoveIsMe ? score : -score;
}

// ============================================================================
// MOVE GENERATION WITH CUT-DISJUNCTION & TOPOLOGICAL ORDERING
// ============================================================================
static int generateMoves2P(Move* outMoves, bool isMe, uint16_t ttBest, uint16_t prevMove, int ply, bool qSearchOnly) {
    int pR = isMe ? myR : oppR;
    int pC = isMe ? myC : oppC;
    int eR = isMe ? oppR : myR;
    int eC = isMe ? oppC : myC;
    int pWalls = isMe ? myWalls : oppWalls;
    int pGoal = isMe ? 0 : (GAME_MODE == 1 ? 0 : B_ROWS - 1);
    int sideIdx = isMe ? 0 : 1;

    const DistCacheEntry& dc = getCachedDistMaps();
    const PathMetrics* pMap = isMe ? dc.me : dc.opp;
    const PathMetrics* eMap = isMe ? dc.opp : dc.me;

    int pIdx = pR * B_COLS + pC;
    int eIdx = eR * B_COLS + eC;
    int curP = pMap[pIdx].dist;
    int curE = eMap[eIdx].dist;
    int curEExits = eMap[eIdx].exits;
    int16_t curEWays = eMap[eIdx].ways;

    uint16_t counterMove = (prevMove < 1024) ? counterMoves[sideIdx][prevMove] : 0;

    int count = 0;

    // 1. Pawn Moves
    int stepCells[8];
    int nSteps = generatePawnSteps2P(pR, pC, eR, eC, stepCells);
    for (int i = 0; i < nSteps; i++) {
        int cell = stepCells[i];
        int sr = cell / B_COLS;
        int sc = cell - sr * B_COLS;
        uint16_t packed = packMove16(STEP, sr, sc, 0);

        if (sr == pGoal) {
            outMoves[0] = {STEP, (uint8_t)sr, (uint8_t)sc, 0, 100000000};
            return 1;
        }

        int newD = pMap[cell].dist;
        int stepGain = curP - newD;

        if (qSearchOnly) {
            bool isJump = (stepGain >= 2) || (abs(pR - eR) + abs(pC - eC) == 1 && stepGain >= 1);
            bool isWinningThreat = (newD <= 1 && curP > 1);
            if (!isJump && !isWinningThreat) continue;
        }

        int32_t ord = stepGain * 16000 + pMap[cell].exits * 350 + historyTable[sideIdx][packed & 1023];
        if (packed == ttBest) ord += 60000000;
        if (packed == counterMove) ord += 14000;
        if (stepGain >= 2) ord += 15000;

        outMoves[count++] = {STEP, (uint8_t)sr, (uint8_t)sc, 0, ord};
    }

    if (pWalls <= 0) {
        sort(outMoves, outMoves + count, [](const Move& a, const Move& b) {
            return a.orderScore > b.orderScore;
        });
        return count;
    }

    // 2. Tactical Wall Placements
    Move wallBuf[256];
    int wCount = 0;
    int maxR = B_ROWS - 2;
    int maxC = B_COLS - 2;

    for (int r = 0; r <= maxR; r++) {
        for (int c = 0; c <= maxC; c++) {
            int idxTL = r * B_COLS + c;
            int dTL = eMap[idxTL].dist;
            int dTR = eMap[idxTL + 1].dist;
            int dBL = eMap[idxTL + B_COLS].dist;
            int dBR = eMap[idxTL + B_COLS + 1].dist;

            bool nearEnemy = (abs(r - eR) <= 3 && abs(c - eC) <= 3);
            bool nearMe = (abs(r - pR) <= 2 && abs(c - pC) <= 2);

            for (int o = 0; o < 2; o++) {
                if (!wallGeometryLegal(r, c, o)) continue;

                bool cutsShortest = false;
                if (o == 0) {
                    cutsShortest = (abs(dTL - dBL) == 1 && min(dTL, dBL) < curE) ||
                                   (abs(dTR - dBR) == 1 && min(dTR, dBR) < curE);
                } else {
                    cutsShortest = (abs(dTL - dTR) == 1 && min(dTL, dTR) < curE) ||
                                   (abs(dBL - dBR) == 1 && min(dBL, dBR) < curE);
                }

                if (!cutsShortest && !nearEnemy && !nearMe) continue;

                placeWallInternal(r, c, o);
                const DistCacheEntry& ndc = getCachedDistMaps();
                const PathMetrics* nPMap = isMe ? ndc.me : ndc.opp;
                const PathMetrics* nEMap = isMe ? ndc.opp : ndc.me;
                int newP = nPMap[pIdx].dist;
                int newE = nEMap[eIdx].dist;

                if (newP < 0 || newE < 0) {
                    removeWallInternal(r, c, o);
                    continue;
                }

                int eGain = newE - curE;
                int pLoss = newP - curP;
                int net = eGain - pLoss;
                int newEExits = nEMap[eIdx].exits;
                int exitDrop = curEExits - newEExits;
                int waysDrop = curEWays - nEMap[eIdx].ways;
                removeWallInternal(r, c, o);

                if (qSearchOnly) {
                    // In Quiescence Search only examine genuinely forcing walls:
                    // walls that force >= 2 step detour, or stop an imminent goal (curE <= 3 && net >= 1)
                    bool forcing = (net >= 2) || (curE <= 3 && net >= 1 && pLoss == 0);
                    if (!forcing) continue;
                } else {
                    // Prune strictly counterproductive walls that neither delay the enemy nor reduce their exits/ways
                    if (net < 0 && exitDrop <= 0) continue;
                    if (net == 0 && exitDrop <= 0 && waysDrop <= 0) continue;
                }

                uint16_t packed = packMove16(WALL, r, c, o);
                // Ordering incorporates Cut Disjunction: a wall that only adds +1 while leaving
                // multiple exits open is ordered below a free pawn step (+16000).
                int32_t ord = net * 9500 + eGain * 3200 + exitDrop * 2600 + (waysDrop > 0 ? 1200 : -1500) + historyTable[sideIdx][packed & 1023];

                if (packed == ttBest) ord += 60000000;
                if (packed == counterMove) ord += 14000;
                if (killerMoves[ply][0] == packed || killerMoves[ply][1] == packed) ord += 11000;

                if (GAME_MODE == 1) {
                    if (o == 1 && abs(c - eC) <= 1 && abs(r - eR) <= 2) ord += 1400;
                    if (pLoss > 0) ord -= pLoss * 3500;
                } else {
                    if (net >= 2 && pLoss == 0) ord += 5500;
                }

                wallBuf[wCount++] = {WALL, (uint8_t)r, (uint8_t)c, (uint8_t)o, ord};
            }
        }
    }

    sort(wallBuf, wallBuf + wCount, [](const Move& a, const Move& b) {
        return a.orderScore > b.orderScore;
    });

    int limit = qSearchOnly ? 6 : (ply == 0 ? 40 : (ply <= 2 ? 20 : 12));
    int take = min(wCount, limit);
    for (int i = 0; i < take; i++) {
        outMoves[count++] = wallBuf[i];
    }

    sort(outMoves, outMoves + count, [](const Move& a, const Move& b) {
        return a.orderScore > b.orderScore;
    });
    return count;
}

static inline uint64_t computeStateKey2P(bool sideToMoveIsMe) {
    uint64_t h = wallZobrist;
    h ^= Z_ME[myR * B_COLS + myC];
    h ^= Z_OPP[oppR * B_COLS + oppC];
    h ^= Z_MW[myWalls];
    h ^= Z_OW[oppWalls];
    if (sideToMoveIsMe) h ^= Z_TURN;
    return h;
}

static inline void storeTT(uint64_t key, int32_t score, int8_t depth, uint8_t flag, uint16_t bestMove) {
    TTCluster& cluster = TT[key & TT_MASK];
    if (cluster.depthPreferred.flag == TT_NONE ||
        cluster.depthPreferred.key == key ||
        depth >= cluster.depthPreferred.depth) {
        cluster.depthPreferred = {key, score, depth, flag, bestMove};
    } else {
        cluster.alwaysReplace = {key, score, depth, flag, bestMove};
    }
}

static inline TTEntry* probeTT(uint64_t key) {
    TTCluster& cluster = TT[key & TT_MASK];
    if (cluster.depthPreferred.flag != TT_NONE && cluster.depthPreferred.key == key) {
        return &cluster.depthPreferred;
    }
    if (cluster.alwaysReplace.flag != TT_NONE && cluster.alwaysReplace.key == key) {
        return &cluster.alwaysReplace;
    }
    return nullptr;
}

// ============================================================================
// QUIESCENCE SEARCH (RESOLVES TACTICAL PAWN JUMPS & FORCING WALL DUELS)
// ============================================================================
static int quiescence2P(int qply, int ply, int alpha, int beta, bool sideToMoveIsMe, uint16_t prevMove) {
    if ((++nodesSearched & 127) == 0 && nowMs() >= searchDeadline) {
        searchAborted = true;
        return 0;
    }

    int oppGoal = (GAME_MODE == 1) ? 0 : B_ROWS - 1;
    if (myR == 0) return sideToMoveIsMe ? (100000 - ply) : -(100000 - ply);
    if (oppR == oppGoal) return sideToMoveIsMe ? -(100000 - ply) : (100000 - ply);

    int standPat = evaluate2P(sideToMoveIsMe);
    if (standPat >= beta) return beta;
    if (standPat > alpha) alpha = standPat;
    if (qply >= 6 || ply >= 60) return alpha;

    Move qMoves[24];
    int nMoves = generateMoves2P(qMoves, sideToMoveIsMe, 0, prevMove, ply, true);
    if (nMoves == 0) return alpha;

    for (int i = 0; i < nMoves; i++) {
        const Move& m = qMoves[i];
        uint16_t mCode = packMove16(m.type, m.r, m.c, m.o);
        int savedR = sideToMoveIsMe ? myR : oppR;
        int savedC = sideToMoveIsMe ? myC : oppC;

        if (m.type == STEP) {
            if (sideToMoveIsMe) { myR = m.r; myC = m.c; }
            else { oppR = m.r; oppC = m.c; }
        } else {
            placeWallInternal(m.r, m.c, m.o);
            if (sideToMoveIsMe) myWalls--; else oppWalls--;
        }

        int score = -quiescence2P(qply + 1, ply + 1, -beta, -alpha, !sideToMoveIsMe, mCode);

        if (m.type == STEP) {
            if (sideToMoveIsMe) { myR = savedR; myC = savedC; }
            else { oppR = savedR; oppC = savedC; }
        } else {
            removeWallInternal(m.r, m.c, m.o);
            if (sideToMoveIsMe) myWalls++; else oppWalls++;
        }

        if (searchAborted) return 0;
        if (score >= beta) return beta;
        if (score > alpha) alpha = score;
    }
    return alpha;
}

// ============================================================================
// PRINCIPAL VARIATION SEARCH (PVS) WITH DYNAMIC LMR & COUNTERMOVE TABLE
// ============================================================================
static int pvs2P(int depth, int ply, int alpha, int beta, bool sideToMoveIsMe, uint16_t prevMove) {
    if ((++nodesSearched & 127) == 0 && nowMs() >= searchDeadline) {
        searchAborted = true;
        return 0;
    }

    int oppGoal = (GAME_MODE == 1) ? 0 : B_ROWS - 1;
    if (myR == 0) return sideToMoveIsMe ? (100000 - ply) : -(100000 - ply);
    if (oppR == oppGoal) return sideToMoveIsMe ? -(100000 - ply) : (100000 - ply);

    if (depth <= 0) {
        return quiescence2P(0, ply, alpha, beta, sideToMoveIsMe, prevMove);
    }

    bool isPvNode = (beta - alpha > 1);
    uint64_t key = computeStateKey2P(sideToMoveIsMe);
    TTEntry* tte = probeTT(key);
    uint16_t ttBest = 0;

    if (tte != nullptr) {
        ttBest = tte->bestMove;
        if (!isPvNode && tte->depth >= depth) {
            if (tte->flag == TT_EXACT) return tte->score;
            if (tte->flag == TT_LOWER && tte->score >= beta) return tte->score;
            if (tte->flag == TT_UPPER && tte->score <= alpha) return tte->score;
        }
    }

    int alphaOrig = alpha;
    Move moves[64];
    int nMoves = generateMoves2P(moves, sideToMoveIsMe, ttBest, prevMove, ply, false);
    if (nMoves == 0) return evaluate2P(sideToMoveIsMe);

    int bestScore = -200000;
    uint16_t bestMoveCode = packMove16(moves[0].type, moves[0].r, moves[0].c, moves[0].o);
    int sideIdx = sideToMoveIsMe ? 0 : 1;

    for (int i = 0; i < nMoves; i++) {
        const Move& m = moves[i];
        uint16_t mCode = packMove16(m.type, m.r, m.c, m.o);
        int savedR = sideToMoveIsMe ? myR : oppR;
        int savedC = sideToMoveIsMe ? myC : oppC;

        if (m.type == STEP) {
            if (sideToMoveIsMe) { myR = m.r; myC = m.c; }
            else { oppR = m.r; oppC = m.c; }
        } else {
            placeWallInternal(m.r, m.c, m.o);
            if (sideToMoveIsMe) myWalls--; else oppWalls--;
        }

        int score;
        if (i == 0) {
            score = -pvs2P(depth - 1, ply + 1, -beta, -alpha, !sideToMoveIsMe, mCode);
        } else {
            int reduction = 0;
            if (depth >= 3 && i >= 4 && m.type == WALL && m.orderScore < 20000) {
                reduction = (depth >= 6 && i >= 10) ? 2 : 1;
            }
            score = -pvs2P(depth - 1 - reduction, ply + 1, -alpha - 1, -alpha, !sideToMoveIsMe, mCode);
            if (!searchAborted && score > alpha && reduction > 0) {
                score = -pvs2P(depth - 1, ply + 1, -alpha - 1, -alpha, !sideToMoveIsMe, mCode);
            }
            if (!searchAborted && score > alpha && score < beta) {
                score = -pvs2P(depth - 1, ply + 1, -beta, -alpha, !sideToMoveIsMe, mCode);
            }
        }

        if (m.type == STEP) {
            if (sideToMoveIsMe) { myR = savedR; myC = savedC; }
            else { oppR = savedR; oppC = savedC; }
        } else {
            removeWallInternal(m.r, m.c, m.o);
            if (sideToMoveIsMe) myWalls++; else oppWalls++;
        }

        if (searchAborted) return 0;

        if (score > bestScore) {
            bestScore = score;
            bestMoveCode = mCode;
        }
        if (score > alpha) alpha = score;
        if (alpha >= beta) {
            if (killerMoves[ply][0] != mCode) {
                killerMoves[ply][1] = killerMoves[ply][0];
                killerMoves[ply][0] = mCode;
            }
            if (prevMove < 1024) {
                counterMoves[sideIdx][prevMove] = mCode;
            }
            historyTable[sideIdx][mCode & 1023] = min(400000, historyTable[sideIdx][mCode & 1023] + depth * depth * 90);
            break;
        }
    }

    uint8_t flag = TT_EXACT;
    if (bestScore <= alphaOrig) flag = TT_UPPER;
    else if (bestScore >= beta) flag = TT_LOWER;
    storeTT(key, bestScore, (int8_t)depth, flag, bestMoveCode);

    return bestScore;
}

// ============================================================================
// QUAD 4-PLAYER ENGINE (11x11 — GOLDEN CENTER 5,5)
// ============================================================================
static bool isOccupiedQuad(int r, int c, int ignoreIdx) {
    for (int i = 0; i < 4; i++) {
        if (i != ignoreIdx && quadP[i].active && quadP[i].r == r && quadP[i].c == c) return true;
    }
    return false;
}

static int getQuadPawnSteps(int pIdx, int* outCells) {
    const QuadPlayer& p = quadP[pIdx];
    int cnt = 0;
    for (int d = 0; d < 4; d++) {
        if (!canStepDir(p.r, p.c, d)) continue;
        int nr = p.r + DR[d], nc = p.c + DC[d];
        if (isOccupiedQuad(nr, nc, pIdx)) {
            int jr = nr + DR[d], jc = nc + DC[d];
            if (jr >= 0 && jr < 11 && jc >= 0 && jc < 11 && canStepDir(nr, nc, d) && !isOccupiedQuad(jr, jc, pIdx)) {
                outCells[cnt++] = jr * 11 + jc;
            } else {
                if (d < 2) {
                    if (canLeft(nr, nc) && !isOccupiedQuad(nr, nc - 1, pIdx)) outCells[cnt++] = nr * 11 + (nc - 1);
                    if (canRight(nr, nc) && !isOccupiedQuad(nr, nc + 1, pIdx)) outCells[cnt++] = nr * 11 + (nc + 1);
                } else {
                    if (canUp(nr, nc) && !isOccupiedQuad(nr - 1, nc, pIdx)) outCells[cnt++] = (nr - 1) * 11 + nc;
                    if (canDown(nr, nc) && !isOccupiedQuad(nr + 1, nc, pIdx)) outCells[cnt++] = (nr + 1) * 11 + nc;
                }
            }
        } else {
            outCells[cnt++] = nr * 11 + nc;
        }
    }
    return cnt;
}

static int evaluateQuad() {
    if (quadP[0].r == 5 && quadP[0].c == 5) return 100000;
    const DistCacheEntry& dc = getCachedDistMaps();
    int myIdx = quadP[0].r * 11 + quadP[0].c;
    int myD = dc.me[myIdx].dist;
    if (myD < 0) return -100000;

    int minOppD = 999;
    int secondOppD = 999;
    int leaderIdx = 1;

    for (int i = 1; i < 4; i++) {
        if (!quadP[i].active) continue;
        if (quadP[i].r == 5 && quadP[i].c == 5) return -100000;
        int od = dc.me[quadP[i].r * 11 + quadP[i].c].dist;
        if (od < 0) return 100000;
        if (od < minOppD) {
            secondOppD = minOppD;
            minOppD = od;
            leaderIdx = i;
        } else if (od < secondOppD) {
            secondOppD = od;
        }
    }

    int myExits = dc.me[myIdx].exits;
    int leadExits = quadP[leaderIdx].active ? dc.me[quadP[leaderIdx].r * 11 + quadP[leaderIdx].c].exits : 2;

    int score = (minOppD - myD) * 1800;
    if (secondOppD < 900) score += (secondOppD - myD) * 450;
    int mwClamped = min(15, max(0, quadP[0].walls));
    score += WALL_MATERIAL_TABLE[mwClamped];
    score += (myExits - leadExits) * 175;
    if (canDown(5, 5) && quadP[0].r > 5) score += 320;
    return score;
}

static int generateQuadMoves(int pIdx, Move* outMoves, bool isRoot) {
    const QuadPlayer& p = quadP[pIdx];
    const DistCacheEntry& dc = getCachedDistMaps();
    int curD = dc.me[p.r * 11 + p.c].dist;
    int count = 0;

    int stepCells[8];
    int nSteps = getQuadPawnSteps(pIdx, stepCells);
    for (int i = 0; i < nSteps; i++) {
        int cell = stepCells[i];
        int sr = cell / 11, sc = cell % 11;
        if (sr == 5 && sc == 5) {
            outMoves[0] = {STEP, (uint8_t)sr, (uint8_t)sc, 0, 100000000};
            return 1;
        }
        int gain = curD - dc.me[cell].dist;
        outMoves[count++] = {STEP, (uint8_t)sr, (uint8_t)sc, 0, gain * 15000 + dc.me[cell].exits * 300};
    }

    if (p.walls <= 0) {
        sort(outMoves, outMoves + count, [](const Move& a, const Move& b) { return a.orderScore > b.orderScore; });
        return count;
    }

    int targetIdx = 0;
    int bestTargetD = 999;
    for (int i = 0; i < 4; i++) {
        if (i == pIdx || !quadP[i].active) continue;
        int d = dc.me[quadP[i].r * 11 + quadP[i].c].dist;
        if (d < bestTargetD) { bestTargetD = d; targetIdx = i; }
    }

    // Targeting Margin: do not waste our 7 walls if no opponent is threatening to beat our race to (5,5)
    if (pIdx == 0 && curD < bestTargetD && bestTargetD > 2) {
        sort(outMoves, outMoves + count, [](const Move& a, const Move& b) { return a.orderScore > b.orderScore; });
        return count;
    }

    const QuadPlayer& target = quadP[targetIdx];
    Move wallBuf[128];
    int wCount = 0;

    for (int r = 0; r <= 9; r++) {
        for (int c = 0; c <= 9; c++) {
            bool nearCenter = (abs(r - 4) <= 2 && abs(c - 4) <= 2);
            bool nearTarget = (abs(r - target.r) <= 2 && abs(c - target.c) <= 2);
            if (!nearCenter && !nearTarget) continue;

            for (int o = 0; o < 2; o++) {
                if (!wallGeometryLegal(r, c, o)) continue;
                placeWallInternal(r, c, o);
                const DistCacheEntry& ndc = getCachedDistMaps();
                bool ok = true;
                for (int i = 0; i < 4; i++) {
                    if (quadP[i].active && ndc.me[quadP[i].r * 11 + quadP[i].c].dist < 0) { ok = false; break; }
                }
                int nMyD = ndc.me[p.r * 11 + p.c].dist;
                int nTarD = ndc.me[target.r * 11 + target.c].dist;
                removeWallInternal(r, c, o);

                if (!ok) continue;
                int delay = nTarD - bestTargetD;
                int loss = nMyD - curD;
                int net = delay - loss;
                if (net <= 0) continue;
                if (pIdx == 0 && net < 2 && bestTargetD > 2) continue;

                int32_t ord = net * 8500 + delay * 2600 + (nearCenter && loss == 0 ? 3200 : 0);
                wallBuf[wCount++] = {WALL, (uint8_t)r, (uint8_t)c, (uint8_t)o, ord};
            }
        }
    }

    sort(wallBuf, wallBuf + wCount, [](const Move& a, const Move& b) { return a.orderScore > b.orderScore; });
    int take = min(wCount, isRoot ? 20 : 8);
    for (int i = 0; i < take; i++) outMoves[count++] = wallBuf[i];

    sort(outMoves, outMoves + count, [](const Move& a, const Move& b) { return a.orderScore > b.orderScore; });
    return count;
}

static int quadMaxSearch(int depth, int alpha, int beta);

static int quadOppRound(int depth, int alpha, int beta) {
    const DistCacheEntry& dc = getCachedDistMaps();
    int leaderIdx = -1, minD = 999;
    for (int i = 1; i < 4; i++) {
        if (!quadP[i].active) continue;
        int d = dc.me[quadP[i].r * 11 + quadP[i].c].dist;
        if (d < minD) { minD = d; leaderIdx = i; }
    }
    if (leaderIdx == -1) return evaluateQuad();

    int savedR[4], savedC[4];
    for (int i = 1; i < 4; i++) {
        savedR[i] = quadP[i].r; savedC[i] = quadP[i].c;
        if (!quadP[i].active || i == leaderIdx) continue;
        int cells[8];
        int n = getQuadPawnSteps(i, cells);
        int bestD = dc.me[quadP[i].r * 11 + quadP[i].c].dist;
        for (int k = 0; k < n; k++) {
            int nd = dc.me[cells[k]].dist;
            if (nd >= 0 && nd < bestD) {
                bestD = nd;
                quadP[i].r = cells[k] / 11;
                quadP[i].c = cells[k] % 11;
            }
        }
    }

    Move lMoves[48];
    int nLM = generateQuadMoves(leaderIdx, lMoves, false);
    int worstForMe = 200000;
    QuadPlayer& lead = quadP[leaderIdx];

    for (int i = 0; i < min(nLM, 10); i++) {
        const Move& m = lMoves[i];
        int sr = lead.r, sc = lead.c;
        if (m.type == STEP) { lead.r = m.r; lead.c = m.c; }
        else { placeWallInternal(m.r, m.c, m.o); lead.walls--; }

        int val = (lead.r == 5 && lead.c == 5) ? -100000 : quadMaxSearch(depth - 1, alpha, min(beta, worstForMe));

        if (m.type == STEP) { lead.r = sr; lead.c = sc; }
        else { removeWallInternal(m.r, m.c, m.o); lead.walls++; }

        if (searchAborted) break;
        if (val < worstForMe) worstForMe = val;
        if (worstForMe <= alpha) break;
    }

    for (int i = 1; i < 4; i++) {
        quadP[i].r = savedR[i]; quadP[i].c = savedC[i];
    }
    return worstForMe;
}

static int quadMaxSearch(int depth, int alpha, int beta) {
    if ((++nodesSearched & 63) == 0 && nowMs() >= searchDeadline) {
        searchAborted = true;
        return 0;
    }
    if (quadP[0].r == 5 && quadP[0].c == 5) return 100000 + depth;
    for (int i = 1; i < 4; i++) {
        if (quadP[i].active && quadP[i].r == 5 && quadP[i].c == 5) return -100000 - depth;
    }
    if (depth <= 0) return evaluateQuad();

    Move myMoves[48];
    int nM = generateQuadMoves(0, myMoves, false);
    if (nM == 0) return evaluateQuad();

    int best = -200000;
    for (int i = 0; i < min(nM, 14); i++) {
        const Move& m = myMoves[i];
        int sr = quadP[0].r, sc = quadP[0].c;
        if (m.type == STEP) { quadP[0].r = m.r; quadP[0].c = m.c; }
        else { placeWallInternal(m.r, m.c, m.o); quadP[0].walls--; }

        int val = (quadP[0].r == 5 && quadP[0].c == 5)
            ? (100000 + depth)
            : quadOppRound(depth - 1, max(alpha, best), beta);

        if (m.type == STEP) { quadP[0].r = sr; quadP[0].c = sc; }
        else { removeWallInternal(m.r, m.c, m.o); quadP[0].walls++; }

        if (searchAborted) return 0;
        if (val > best) best = val;
        if (best >= beta) break;
    }
    return best;
}

extern "C" {

EMSCRIPTEN_KEEPALIVE
void initEngine() {
    initTables();
    memset(TT, 0, sizeof(TT));
    memset(DistCache, 0, sizeof(DistCache));
}

EMSCRIPTEN_KEEPALIVE
int getNodesSearched() {
    return (int)nodesSearched;
}

EMSCRIPTEN_KEEPALIVE
int getCompletedDepth() {
    return completedDepthGlobal;
}

EMSCRIPTEN_KEEPALIVE
int search(int mode, int rows, int cols,
           int mR, int mC, int mW,
           int oR, int oC, int oW,
           const char* wallListStr,
           const char* quadStr,
           int timeMs, int maxDepth) {

    GAME_MODE = mode;
    B_ROWS = rows;
    B_COLS = cols;
    myR = mR; myC = mC; myWalls = mW;
    oppR = oR; oppC = oC; oppWalls = oW;

    memset(hWalls, 0, sizeof(hWalls));
    memset(vWalls, 0, sizeof(vWalls));
    memset(killerMoves, 0, sizeof(killerMoves));
    memset(counterMoves, 0, sizeof(counterMoves));
    memset(historyTable, 0, sizeof(historyTable));
    wallZobrist = 0;
    totalWallsOnBoard = 0;

    if (wallListStr && strlen(wallListStr) > 0) {
        char buf[4096];
        strncpy(buf, wallListStr, sizeof(buf) - 1);
        buf[sizeof(buf) - 1] = '\0';
        char* token = strtok(buf, ";");
        while (token) {
            int wr, wc; char wo;
            if (sscanf(token, "%d,%d,%c", &wr, &wc, &wo) == 3) {
                placeWallInternal(wr, wc, (wo == 'h' ? 0 : 1));
            }
            token = strtok(nullptr, ";");
        }
    }

    nodesSearched = 0;
    completedDepthGlobal = 0;
    searchAborted = false;
    searchDeadline = nowMs() + timeMs;

    if (GAME_MODE == 2 && quadStr && strlen(quadStr) > 0) {
        char qbuf[512];
        strncpy(qbuf, quadStr, sizeof(qbuf) - 1);
        qbuf[sizeof(qbuf) - 1] = '\0';
        char* tok = strtok(qbuf, ";");
        int idx = 0;
        while (tok && idx < 4) {
            int qr, qc, qw, qa;
            if (sscanf(tok, "%d,%d,%d,%d", &qr, &qc, &qw, &qa) == 4) {
                quadP[idx] = {qr, qc, qw, qa != 0};
            }
            tok = strtok(nullptr, ";");
            idx++;
        }

        Move rootMoves[64];
        int nRoot = generateQuadMoves(0, rootMoves, true);
        if (nRoot == 0) return 0;
        Move bestMove = rootMoves[0];
        if (bestMove.type == STEP && bestMove.r == 5 && bestMove.c == 5) {
            completedDepthGlobal = 1;
            return packMove16(bestMove.type, bestMove.r, bestMove.c, bestMove.o);
        }

        for (int d = 1; d <= min(maxDepth, 7); d++) {
            if (nowMs() >= searchDeadline) break;
            searchAborted = false;
            Move iterBest = bestMove;
            int iterScore = -200000;

            for (int i = 0; i < nRoot; i++) {
                const Move& m = rootMoves[i];
                int sr = quadP[0].r, sc = quadP[0].c;
                if (m.type == STEP) { quadP[0].r = m.r; quadP[0].c = m.c; }
                else { placeWallInternal(m.r, m.c, m.o); quadP[0].walls--; }

                int scVal = quadOppRound(d - 1, iterScore, 200000);

                if (m.type == STEP) { quadP[0].r = sr; quadP[0].c = sc; }
                else { removeWallInternal(m.r, m.c, m.o); quadP[0].walls++; }

                if (searchAborted) break;
                if (scVal > iterScore) { iterScore = scVal; iterBest = m; }
            }
            if (!searchAborted) {
                bestMove = iterBest;
                completedDepthGlobal = d;
                if (iterScore >= 90000) break;
            } else break;
        }
        return packMove16(bestMove.type, bestMove.r, bestMove.c, bestMove.o);
    }

    Move rootMoves[64];
    int nRoot = generateMoves2P(rootMoves, true, 0, 0, 0, false);
    if (nRoot == 0) return 0;

    Move bestMove = rootMoves[0];
    if (bestMove.type == STEP && bestMove.r == 0) {
        completedDepthGlobal = 1;
        return packMove16(bestMove.type, bestMove.r, bestMove.c, bestMove.o);
    }

    int prevScore = evaluate2P(true);

    // Iterative Deepening with Aspiration Windows
    for (int d = 1; d <= maxDepth; d++) {
        if (nowMs() >= searchDeadline) break;
        searchAborted = false;

        int delta = 650;
        int alpha = (d >= 3) ? max(-200000, prevScore - delta) : -200000;
        int beta  = (d >= 3) ? min(200000, prevScore + delta)  : 200000;

        Move iterBest = bestMove;
        int iterBestScore = -200000;

        while (true) {
            // Put current PV move first
            for (int i = 1; i < nRoot; i++) {
                if (rootMoves[i].type == bestMove.type &&
                    rootMoves[i].r == bestMove.r &&
                    rootMoves[i].c == bestMove.c &&
                    rootMoves[i].o == bestMove.o) {
                    swap(rootMoves[0], rootMoves[i]);
                    break;
                }
            }

            int curAlpha = alpha;
            iterBestScore = -200000;
            iterBest = rootMoves[0];

            for (int i = 0; i < nRoot; i++) {
                const Move& m = rootMoves[i];
                uint16_t mCode = packMove16(m.type, m.r, m.c, m.o);
                int savedR = myR, savedC = myC;
                if (m.type == STEP) { myR = m.r; myC = m.c; }
                else { placeWallInternal(m.r, m.c, m.o); myWalls--; }

                int score;
                if (i == 0) {
                    score = -pvs2P(d - 1, 1, -beta, -curAlpha, false, mCode);
                } else {
                    score = -pvs2P(d - 1, 1, -curAlpha - 1, -curAlpha, false, mCode);
                    if (!searchAborted && score > curAlpha && score < beta) {
                        score = -pvs2P(d - 1, 1, -beta, -curAlpha, false, mCode);
                    }
                }

                if (m.type == STEP) { myR = savedR; myC = savedC; }
                else { removeWallInternal(m.r, m.c, m.o); myWalls++; }

                if (searchAborted) break;
                if (score > iterBestScore) {
                    iterBestScore = score;
                    iterBest = m;
                }
                if (score > curAlpha) curAlpha = score;
                if (curAlpha >= beta) break;
            }

            if (searchAborted) break;

            if (iterBestScore <= alpha) {
                alpha = max(-200000, iterBestScore - delta);
                delta *= 2;
            } else if (iterBestScore >= beta) {
                bestMove = iterBest;
                beta = min(200000, iterBestScore + delta);
                delta *= 2;
            } else {
                break;
            }
        }

        if (!searchAborted) {
            bestMove = iterBest;
            prevScore = iterBestScore;
            completedDepthGlobal = d;
            if (iterBestScore >= 90000) break;
        } else {
            break;
        }
    }

    return packMove16(bestMove.type, bestMove.r, bestMove.c, bestMove.o);
}

}
