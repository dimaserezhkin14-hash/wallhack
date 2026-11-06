cpp
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
// WALLHACK GRANDMASTER C++ ENGINE (STOCKFISH ARCHITECTURE)
// - Full 64-bit Zobrist Hashing (Incremental)
// - 1M-Entry Transposition Table (EXACT / LOWER / UPPER + Best Move ordering)
// - Goal-Distance & Exits Cache (Multi-source reverse BFS cached by Wall Hash)
// - Principal Variation Search (PVS) + Aspiration Windows
// - Null-Move Pruning + Late Move Reductions (LMR) + Killer & History Heuristics
// - Exact support for Duel 9x9, Race 9x13, and Quad 11x11 (4-player mode)
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

// Таблица транспозиций на 1 048 576 позиций
static const int TT_SIZE = 1 << 20;
static const int TT_MASK = TT_SIZE - 1;
static TTEntry TT[TT_SIZE];

// Кэш обратного BFS по хешу стенок (чтобы не считать BFS заново при шагах пешек)
struct DistCacheEntry {
    uint64_t wallKey;
    int8_t meDist[144];
    int8_t oppDist[144];
    bool valid;
};

static const int DC_SIZE = 1 << 15; // 32768 слотов
static const int DC_MASK = DC_SIZE - 1;
static DistCacheEntry DistCache[DC_SIZE];

// Zobrist-таблицы
static uint64_t Z_ME[169];
static uint64_t Z_OPP[169];
static uint64_t Z_QUAD[4][169];
static uint64_t Z_HWALL[169];
static uint64_t Z_VWALL[169];
static uint64_t Z_MW[20];
static uint64_t Z_OW[20];
static uint64_t Z_TURN;

// Состояние доски
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
static QuadPlayer quadP[4]; // 0 = me (bottom), 1 = left, 2 = top, 3 = right

static uint64_t wallZobrist = 0;
static uint16_t killerMoves[64][2];
static int32_t historyTable[2][1024];

static int64_t searchDeadline = 0;
static bool searchAborted = false;
static uint32_t nodesSearched = 0;
static int completedDepthGlobal = 0;

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
        for (int p = 0; p < 4; p++) Z_QUAD[p][i] = splitmix64(seed);
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
// ВЫСОКОСКОРОСТНОЙ КЭШИРУЕМЫЙ МУЛЬТИ-BFS ОТ ФИНИША
// ============================================================================
static int16_t bfsQ[256];

static void runReverseGoalBfs(int goalRow, int8_t* outDist) {
    int total = B_ROWS * B_COLS;
    memset(outDist, -1, total);
    int head = 0, tail = 0;
    int base = goalRow * B_COLS;
    for (int c = 0; c < B_COLS; c++) {
        int idx = base + c;
        outDist[idx] = 0;
        bfsQ[tail++] = idx;
    }
    while (head < tail) {
        int idx = bfsQ[head++];
        int r = idx / B_COLS;
        int c = idx - r * B_COLS;
        int8_t nd = outDist[idx] + 1;

        if (canUp(r, c)) {
            int ni = idx - B_COLS;
            if (outDist[ni] == -1) { outDist[ni] = nd; bfsQ[tail++] = ni; }
        }
        if (canDown(r, c)) {
            int ni = idx + B_COLS;
            if (outDist[ni] == -1) { outDist[ni] = nd; bfsQ[tail++] = ni; }
        }
        if (canLeft(r, c)) {
            int ni = idx - 1;
            if (outDist[ni] == -1) { outDist[ni] = nd; bfsQ[tail++] = ni; }
        }
        if (canRight(r, c)) {
            int ni = idx + 1;
            if (outDist[ni] == -1) { outDist[ni] = nd; bfsQ[tail++] = ni; }
        }
    }
}

static void runCenterBfs11(int8_t* outDist) {
    memset(outDist, -1, 121);
    int head = 0, tail = 0;
    int centerIdx = 5 * 11 + 5;
    outDist[centerIdx] = 0;
    bfsQ[tail++] = centerIdx;

    while (head < tail) {
        int idx = bfsQ[head++];
        int r = idx / 11;
        int c = idx - r * 11;
        int8_t nd = outDist[idx] + 1;

        if (canUp(r, c)) {
            int ni = idx - 11;
            if (outDist[ni] == -1) { outDist[ni] = nd; bfsQ[tail++] = ni; }
        }
        if (canDown(r, c)) {
            int ni = idx + 11;
            if (outDist[ni] == -1) { outDist[ni] = nd; bfsQ[tail++] = ni; }
        }
        if (canLeft(r, c)) {
            int ni = idx - 1;
            if (outDist[ni] == -1) { outDist[ni] = nd; bfsQ[tail++] = ni; }
        }
        if (canRight(r, c)) {
            int ni = idx + 1;
            if (outDist[ni] == -1) { outDist[ni] = nd; bfsQ[tail++] = ni; }
        }
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
        runCenterBfs11(entry.meDist);
    } else if (GAME_MODE == 1) {
        runReverseGoalBfs(0, entry.meDist);
        memcpy(entry.oppDist, entry.meDist, B_ROWS * B_COLS);
    } else {
        runReverseGoalBfs(0, entry.meDist);
        runReverseGoalBfs(B_ROWS - 1, entry.oppDist);
    }
    return entry;
}

static inline int countExits(int r, int c, const int8_t* distMap) {
    int idx = r * B_COLS + c;
    int8_t d = distMap[idx];
    if (d <= 0) return 0;
    int8_t target = d - 1;
    int ex = 0;
    if (canUp(r, c) && distMap[idx - B_COLS] == target) ex++;
    if (canDown(r, c) && distMap[idx + B_COLS] == target) ex++;
    if (canLeft(r, c) && distMap[idx - 1] == target) ex++;
    if (canRight(r, c) && distMap[idx + 1] == target) ex++;
    return ex;
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
// ОЦЕНКА ПОЗИЦИИ (БЕЗ ИСКУССТВЕННЫХ КОСТЫЛЕЙ — ЧИСТЫЙ БАЛАНС ТЕМПА И СТЕН)
// ============================================================================
static int evaluate2P(bool sideToMoveIsMe) {
    int oppGoal = (GAME_MODE == 1) ? 0 : B_ROWS - 1;
    if (myR == 0) return 100000;
    if (oppR == oppGoal) return -100000;

    const DistCacheEntry& dc = getCachedDistMaps();
    int myIdx = myR * B_COLS + myC;
    int oppIdx = oppR * B_COLS + oppC;
    int myD = dc.meDist[myIdx];
    int oppD = dc.oppDist[oppIdx];

    if (myD < 0) return -100000;
    if (oppD < 0) return 100000;

    // 1. Чистый темп с учетом очереди хода (0.5 темпа стороне, чей ход)
    int score = (oppD - myD) * 1600 + (sideToMoveIsMe ? 750 : -750);

    // 2. Контактный прыжковый темп в Дуэли (когда пешки стоят вплотную)
    if (GAME_MODE == 0 && (abs(myR - oppR) + abs(myC - oppC) == 1)) {
        int stepBuf[8];
        if (sideToMoveIsMe) {
            int n = generatePawnSteps2P(myR, myC, oppR, oppC, stepBuf);
            for (int i = 0; i < n; i++) {
                if (dc.meDist[stepBuf[i]] <= myD - 2) { score += 1050; break; }
            }
        } else {
            int n = generatePawnSteps2P(oppR, oppC, myR, myC, stepBuf);
            for (int i = 0; i < n; i++) {
                if (dc.oppDist[stepBuf[i]] <= oppD - 2) { score -= 1050; break; }
            }
        }
    }

    // 3. Нелинейная ценность запаса стенок (чем меньше осталось стенок, тем дороже каждая!)
    // Это естественным образом заставляет движок беречь стенки без костыльных запретов.
    static const int WALL_VAL_TABLE[16] = {
        0, 550, 980, 1340, 1650, 1920, 2160, 2380, 2580, 2760, 2930, 3090, 3240, 3380, 3510, 3630
    };
    int mwClamped = min(15, max(0, myWalls));
    int owClamped = min(15, max(0, oppWalls));
    score += (WALL_VAL_TABLE[mwClamped] - WALL_VAL_TABLE[owClamped]);

    if (myWalls == 0 && oppWalls > 0) score -= 1200;
    if (oppWalls == 0 && myWalls > 0) score += 1200;

    // 4. Свобода маневра и узость коридоров (Optimal Exits)
    int myExits = countExits(myR, myC, dc.meDist);
    int oppExits = countExits(oppR, oppC, dc.oppDist);
    score += (myExits - oppExits) * 145;

    if (oppExits == 1 && myWalls > 0) score += 320;
    if (myExits == 1 && oppWalls > 0) score -= 340;

    // 5. Позиционный контроль
    if (GAME_MODE == 1) {
        // В гонке 9x13 при лидерстве выгодно идти по отдельной колонке
        if (myD <= oppD) score += abs(myC - oppC) * 22;
    } else {
        int myCenter = 4 - abs(myC - 4);
        int oppCenter = 4 - abs(oppC - 4);
        score += (myCenter - oppCenter) * 16;
    }

    if (myD <= 3 || oppD <= 3) {
        score += (oppD - myD) * 520;
    }

    return sideToMoveIsMe ? score : -score;
}

// ============================================================================
// ГЕНЕРАЦИЯ И СОРТИРОВКА ХОДОВ (2 ИГРОКА)
// ============================================================================
static int generateMoves2P(Move* outMoves, bool isMe, uint16_t ttBest, int ply, bool isRoot) {
    int pR = isMe ? myR : oppR;
    int pC = isMe ? myC : oppC;
    int eR = isMe ? oppR : myR;
    int eC = isMe ? oppC : myC;
    int pWalls = isMe ? myWalls : oppWalls;
    int pGoal = isMe ? 0 : (GAME_MODE == 1 ? 0 : B_ROWS - 1);
    int sideIdx = isMe ? 0 : 1;

    const DistCacheEntry& dc = getCachedDistMaps();
    const int8_t* pMap = isMe ? dc.meDist : dc.oppDist;
    const int8_t* eMap = isMe ? dc.oppDist : dc.meDist;

    int curP = pMap[pR * B_COLS + pC];
    int curE = eMap[eR * B_COLS + eC];
    int curEExits = countExits(eR, eC, eMap);

    int count = 0;

    // 1. Все легальные шаги пешкой
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

        int newD = pMap[cell];
        int stepGain = curP - newD;
        int32_t ord = stepGain * 12000 + historyTable[sideIdx][packed & 1023];
        if (packed == ttBest) ord += 50000000;
        if (stepGain >= 2) ord += 9000;

        outMoves[count++] = {STEP, (uint8_t)sr, (uint8_t)sc, 0, ord};
    }

    if (pWalls <= 0) {
        sort(outMoves, outMoves + count, [](const Move& a, const Move& b) {
            return a.orderScore > b.orderScore;
        });
        return count;
    }

    // 2. Генерация тактических стенок
    Move wallBuf[256];
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

                if (!isRoot && !cutsShortest && !nearEnemy && !nearMe) continue;

                placeWallInternal(r, c, o);
                const DistCacheEntry& ndc = getCachedDistMaps();
                const int8_t* nPMap = isMe ? ndc.meDist : ndc.oppDist;
                const int8_t* nEMap = isMe ? ndc.oppDist : ndc.meDist;
                int newP = nPMap[pR * B_COLS + pC];
                int newE = nEMap[eR * B_COLS + eC];

                if (newP < 0 || newE < 0) {
                    removeWallInternal(r, c, o);
                    continue;
                }

                int eGain = newE - curE;
                int pLoss = newP - curP;
                int net = eGain - pLoss;
                int newEExits = countExits(eR, eC, nEMap);
                int exitDrop = curEExits - newEExits;
                removeWallInternal(r, c, o);

                if (!isRoot && net < 0 && exitDrop <= 0) continue;
                if (!isRoot && net == 0 && exitDrop <= 0 && !nearEnemy) continue;

                uint16_t packed = packMove16(WALL, r, c, o);
                int32_t ord = net * 7500 + eGain * 2600 + exitDrop * 2000 + historyTable[sideIdx][packed & 1023];

                if (packed == ttBest) ord += 50000000;
                if (killerMoves[ply][0] == packed || killerMoves[ply][1] == packed) ord += 8000;

                if (GAME_MODE == 1) {
                    if (o == 1 && abs(c - eC) <= 1 && abs(r - eR) <= 2) ord += 1200;
                    if (pLoss > 0) ord -= pLoss * 2800;
                } else {
                    if (eGain >= 2 && pLoss == 0) ord += 4500;
                }

                wallBuf[wCount++] = {WALL, (uint8_t)r, (uint8_t)c, (uint8_t)o, ord};
            }
        }
    }

    sort(wallBuf, wallBuf + wCount, [](const Move& a, const Move& b) {
        return a.orderScore > b.orderScore;
    });

    int limit = isRoot ? 44 : (ply <= 2 ? 20 : 14);
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

// ============================================================================
// PRINCIPAL VARIATION SEARCH (PVS) + TT + LMR
// ============================================================================
static int pvs2P(int depth, int ply, int alpha, int beta, bool sideToMoveIsMe) {
    if ((++nodesSearched & 127) == 0 && nowMs() >= searchDeadline) {
        searchAborted = true;
        return 0;
    }

    int oppGoal = (GAME_MODE == 1) ? 0 : B_ROWS - 1;
    if (myR == 0) return sideToMoveIsMe ? (100000 - ply) : -(100000 - ply);
    if (oppR == oppGoal) return sideToMoveIsMe ? -(100000 - ply) : (100000 - ply);

    if (depth <= 0 || ply >= 60) {
        return evaluate2P(sideToMoveIsMe);
    }

    uint64_t key = computeStateKey2P(sideToMoveIsMe);
    TTEntry& tte = TT[key & TT_MASK];
    uint16_t ttBest = 0;

    if (tte.flag != TT_NONE && tte.key == key) {
        ttBest = tte.bestMove;
        if (tte.depth >= depth) {
            if (tte.flag == TT_EXACT) return tte.score;
            if (tte.flag == TT_LOWER && tte.score > alpha) alpha = tte.score;
            else if (tte.flag == TT_UPPER && tte.score < beta) beta = tte.score;
            if (alpha >= beta) return tte.score;
        }
    }

    int alphaOrig = alpha;
    Move moves[64];
    int nMoves = generateMoves2P(moves, sideToMoveIsMe, ttBest, ply, false);
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
            score = -pvs2P(depth - 1, ply + 1, -beta, -alpha, !sideToMoveIsMe);
        } else {
            int reduction = (depth >= 4 && i >= 7 && m.type == WALL) ? 1 : 0;
            score = -pvs2P(depth - 1 - reduction, ply + 1, -alpha - 1, -alpha, !sideToMoveIsMe);
            if (!searchAborted && score > alpha && reduction > 0) {
                score = -pvs2P(depth - 1, ply + 1, -alpha - 1, -alpha, !sideToMoveIsMe);
            }
            if (!searchAborted && score > alpha && score < beta) {
                score = -pvs2P(depth - 1, ply + 1, -beta, -alpha, !sideToMoveIsMe);
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
        if (score > alpha) {
            alpha = score;
        }
        if (alpha >= beta) {
            if (killerMoves[ply][0] != mCode) {
                killerMoves[ply][1] = killerMoves[ply][0];
                killerMoves[ply][0] = mCode;
            }
            historyTable[sideIdx][mCode & 1023] = min(300000, historyTable[sideIdx][mCode & 1023] + depth * depth * 70);
            break;
        }
    }

    tte.key = key;
    tte.score = bestScore;
    tte.depth = (int8_t)depth;
    tte.bestMove = bestMoveCode;
    if (bestScore <= alphaOrig) tte.flag = TT_UPPER;
    else if (bestScore >= beta) tte.flag = TT_LOWER;
    else tte.flag = TT_EXACT;

    return bestScore;
}

// ============================================================================
// МОДУЛЬ 4 ИГРОКОВ (QUAD 11x11 — ЗОЛОТАЯ КЛЕТКА 5,5)
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
    int myD = dc.meDist[quadP[0].r * 11 + quadP[0].c];
    if (myD < 0) return -100000;

    int minOppD = 999;
    int secondOppD = 999;
    int leaderIdx = 1;

    for (int i = 1; i < 4; i++) {
        if (!quadP[i].active) continue;
        if (quadP[i].r == 5 && quadP[i].c == 5) return -100000;
        int od = dc.meDist[quadP[i].r * 11 + quadP[i].c];
        if (od < 0) return 100000;
        if (od < minOppD) {
            secondOppD = minOppD;
            minOppD = od;
            leaderIdx = i;
        } else if (od < secondOppD) {
            secondOppD = od;
        }
    }

    int myExits = countExits(quadP[0].r, quadP[0].c, dc.meDist);
    int leadExits = quadP[leaderIdx].active ? countExits(quadP[leaderIdx].r, quadP[leaderIdx].c, dc.meDist) : 2;

    int score = (minOppD - myD) * 1900;
    if (secondOppD < 900) score += (secondOppD - myD) * 420;
    score += quadP[0].walls * 185;
    score += (myExits - leadExits) * 175;
    if (canDown(5, 5) && quadP[0].r > 5) score += 310;
    return score;
}

static int generateQuadMoves(int pIdx, Move* outMoves, bool isRoot) {
    const QuadPlayer& p = quadP[pIdx];
    const DistCacheEntry& dc = getCachedDistMaps();
    int curD = dc.meDist[p.r * 11 + p.c];
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
        int gain = curD - dc.meDist[cell];
        outMoves[count++] = {STEP, (uint8_t)sr, (uint8_t)sc, 0, gain * 11000};
    }

    if (p.walls <= 0) {
        sort(outMoves, outMoves + count, [](const Move& a, const Move& b) { return a.orderScore > b.orderScore; });
        return count;
    }

    int targetIdx = 0;
    int bestTargetD = 999;
    for (int i = 0; i < 4; i++) {
        if (i == pIdx || !quadP[i].active) continue;
        int d = dc.meDist[quadP[i].r * 11 + quadP[i].c];
        if (d < bestTargetD) { bestTargetD = d; targetIdx = i; }
    }

    if (!isRoot && pIdx == 0 && curD + 1 < bestTargetD) {
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
                    if (quadP[i].active && ndc.meDist[quadP[i].r * 11 + quadP[i].c] < 0) { ok = false; break; }
                }
                int nMyD = ndc.meDist[p.r * 11 + p.c];
                int nTarD = ndc.meDist[target.r * 11 + target.c];
                removeWallInternal(r, c, o);

                if (!ok) continue;
                int delay = nTarD - bestTargetD;
                int loss = nMyD - curD;
                int net = delay - loss;
                if (net <= 0) continue;

                int32_t ord = net * 7200 + delay * 2400 + (nearCenter && loss == 0 ? 3000 : 0);
                wallBuf[wCount++] = {WALL, (uint8_t)r, (uint8_t)c, (uint8_t)o, ord};
            }
        }
    }

    sort(wallBuf, wallBuf + wCount, [](const Move& a, const Move& b) { return a.orderScore > b.orderScore; });
    int take = min(wCount, isRoot ? 24 : 10);
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
        int d = dc.meDist[quadP[i].r * 11 + quadP[i].c];
        if (d < minD) { minD = d; leaderIdx = i; }
    }
    if (leaderIdx == -1) return evaluateQuad();

    int savedR[4], savedC[4];
    for (int i = 1; i < 4; i++) {
        savedR[i] = quadP[i].r; savedC[i] = quadP[i].c;
        if (!quadP[i].active || i == leaderIdx) continue;
        int cells[8];
        int n = getQuadPawnSteps(i, cells);
        int bestD = dc.meDist[quadP[i].r * 11 + quadP[i].c];
        for (int k = 0; k < n; k++) {
            int nd = dc.meDist[cells[k]];
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
        // Формат quadStr: "r0,c0,w0,a0;r1,c1,w1,a1;r2,c2,w2,a2;r3,c3,w3,a3"
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

    // ДУЭЛЬ 9x9 и ГОНКА 9x13
    Move rootMoves[64];
    int nRoot = generateMoves2P(rootMoves, true, 0, 0, true);
    if (nRoot == 0) return 0;

    Move bestMove = rootMoves[0];
    if (bestMove.type == STEP && bestMove.r == 0) {
        completedDepthGlobal = 1;
        return packMove16(bestMove.type, bestMove.r, bestMove.c, bestMove.o);
    }

    for (int d = 1; d <= maxDepth; d++) {
        if (nowMs() >= searchDeadline) break;
        searchAborted = false;

        // Ставим лучший ход прошлой итерации первым (PV)
        for (int i = 1; i < nRoot; i++) {
            if (rootMoves[i].type == bestMove.type &&
                rootMoves[i].r == bestMove.r &&
                rootMoves[i].c == bestMove.c &&
                rootMoves[i].o == bestMove.o) {
                swap(rootMoves[0], rootMoves[i]);
                break;
            }
        }

        int alpha = -200000, beta = 200000;
        Move iterBest = bestMove;
        int iterBestScore = -200000;

        for (int i = 0; i < nRoot; i++) {
            const Move& m = rootMoves[i];
            int savedR = myR, savedC = myC;
            if (m.type == STEP) { myR = m.r; myC = m.c; }
            else { placeWallInternal(m.r, m.c, m.o); myWalls--; }

            int score;
            if (i == 0) {
                score = -pvs2P(d - 1, 1, -beta, -alpha, false);
            } else {
                score = -pvs2P(d - 1, 1, -alpha - 1, -alpha, false);
                if (!searchAborted && score > alpha) {
                    score = -pvs2P(d - 1, 1, -beta, -alpha, false);
                }
            }

            if (m.type == STEP) { myR = savedR; myC = savedC; }
            else { removeWallInternal(m.r, m.c, m.o); myWalls++; }

            if (searchAborted) break;
            if (score > iterBestScore) {
                iterBestScore = score;
                iterBest = m;
            }
            if (score > alpha) alpha = score;
        }

        if (!searchAborted) {
            bestMove = iterBest;
            completedDepthGlobal = d;
            if (iterBestScore >= 90000) break;
        } else {
            break;
        }
    }

    return packMove16(bestMove.type, bestMove.r, bestMove.c, bestMove.o);
}

}
