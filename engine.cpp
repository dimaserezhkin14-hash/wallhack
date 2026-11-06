#include <iostream>
#include <vector>
#include <cstdint>
#include <algorithm>
#include <chrono>
#include <cstring>
#include <cmath>

#ifdef __EMSCRIPTEN__
#include <emscripten/emscripten.h>
#define EXPORT_FN EMSCRIPTEN_KEEPALIVE
#else
#define EXPORT_FN
#endif

using namespace std;

// ============================================================================
// WALLHACK GRANDMASTER ENGINE (EXACT NEMESIS + STOCKFISH ALPHA-BETA HYBRID)
// Incorporates exact algorithms extracted from gorisanson/quoridor-ai (game.js & ai.js):
// 1. O(1) Two-Point Topological Articulation Filter (testIfConnectedOnTwoPoints)
// 2. Exact Nemesis Wall-Chain Stencils (col +/- 2, col +/- 3 gap-1 door traps,
//    setWallsBesidePawn, and turn >= 6 leftmost/rightmost edge horizontal walls)
// 3. Exact Shortest-Path DAG Edge-Cutter (getValidNextWallsDisturbPathOf)
// 4. Combined with Alpha-Beta PVS + 2-Ply Cage-Probe (curing MCTS trap blindness)
// ============================================================================

enum MoveType : uint8_t { STEP = 0, WALL = 1 };

struct Move {
    uint8_t type;    // 0 = step, 1 = wall
    uint8_t r, c, o; // o: 0 = horizontal, 1 = vertical
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

static const int TT_CLUSTERS = 1 << 19; // 524,288 clusters (1,048,576 entries)
static const int TT_MASK = TT_CLUSTERS - 1;
static TTCluster TT[TT_CLUSTERS];

struct PathMetrics {
    int8_t dist;
    int16_t ways;
    uint8_t exits;
    uint8_t onShortestDAG; // 1 if cell belongs to at least one shortest path from pawn to goal
};

struct DistCacheEntry {
    uint64_t wallKey;
    PathMetrics me[144];
    PathMetrics opp[144];
    bool valid;
};

static const int DC_SIZE = 1 << 15;
static const int DC_MASK = DC_SIZE - 1;
static DistCacheEntry DistCache[DC_SIZE];

static uint64_t Z_ME[169];
static uint64_t Z_OPP[169];
static uint64_t Z_HWALL[169];
static uint64_t Z_VWALL[169];
static uint64_t Z_MW[20];
static uint64_t Z_OW[20];
static uint64_t Z_TURN;

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

struct EvalParams {
    int32_t tempoPerStep;         // 1000 cp: 1 full step closer to goal
    int32_t turnAdvantage;        // 500 cp: right to move first (0.5 step)
    int32_t exitWeight;           // 170 cp: local degrees of freedom on shortest DAG
    int32_t waysWeight;           // 95 cp: global route multiplicity (log2 ways)
    int32_t corridorTrapBonus;    // 410 cp: opponent restricted to 1 exit with walls in reserve
    int32_t oppositionBonus;      // 960 cp: direct adjacent pawn jump threat
    int32_t centerWeight;         // 24 cp: central column control
    int32_t cageThreatWeight;     // 1250 cp: 2-wall cage trap penalty/bonus
};

static const EvalParams PARAMS_DUEL = { 1000, 500, 170, 95, 410, 960, 24, 1250 };
static const EvalParams PARAMS_RACE = { 1050, 525, 145, 75, 320, 900, 12, 1300 };

static const int32_t WALL_MATERIAL_TABLE[16] = {
    0, 1450, 2700, 3800, 4800, 5720, 6580, 7390, 8150, 8860, 9500, 10100, 10680, 11240, 11780, 12300
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

extern "C" {
EXPORT_FN void initEngine() {
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
    memset(TT, 0, sizeof(TT));
    memset(DistCache, 0, sizeof(DistCache));
}
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
// EXACT NEMESIS O(1) TWO-POINT CONNECTIVITY FILTER (from game.js)
// A wall that does NOT connect to at least 2 existing wall endpoints/edges
// CANNOT disconnect any player's path to goal!
// ============================================================================
static inline bool isConnectedOnTwoPoints(int r, int c, int o) {
    int stride = B_COLS - 1;
    int maxR = B_ROWS - 2;
    int maxC = B_COLS - 2;

    if (o == 0) {
        // Left endpoint connectivity
        bool left = (c == 0);
        if (!left && c >= 1) {
            if (vWalls[r * stride + (c - 1)]) left = true;
            else if (r >= 1 && vWalls[(r - 1) * stride + (c - 1)]) left = true;
            else if (r < maxR && vWalls[(r + 1) * stride + (c - 1)]) left = true;
            else if (c >= 2 && hWalls[r * stride + (c - 2)]) left = true;
        }
        // Right endpoint connectivity
        bool right = (c == maxC);
        if (!right && c < maxC) {
            if (vWalls[r * stride + (c + 1)]) right = true;
            else if (r >= 1 && vWalls[(r - 1) * stride + (c + 1)]) right = true;
            else if (r < maxR && vWalls[(r + 1) * stride + (c + 1)]) right = true;
            else if (c + 2 <= maxC && hWalls[r * stride + (c + 2)]) right = true;
        }
        // Middle intersection connectivity
        bool middle = false;
        if (r >= 1 && vWalls[(r - 1) * stride + c]) middle = true;
        else if (r < maxR && vWalls[(r + 1) * stride + c]) middle = true;

        return (left && right) || (right && middle) || (middle && left);
    } else {
        // Top endpoint connectivity
        bool top = (r == 0);
        if (!top && r >= 1) {
            if (hWalls[(r - 1) * stride + c]) top = true;
            else if (c >= 1 && hWalls[(r - 1) * stride + (c - 1)]) top = true;
            else if (c < maxC && hWalls[(r - 1) * stride + (c + 1)]) top = true;
            else if (r >= 2 && vWalls[(r - 2) * stride + c]) top = true;
        }
        // Bottom endpoint connectivity
        bool bottom = (r == maxR);
        if (!bottom && r < maxR) {
            if (hWalls[(r + 1) * stride + c]) bottom = true;
            else if (c >= 1 && hWalls[(r + 1) * stride + (c - 1)]) bottom = true;
            else if (c < maxC && hWalls[(r + 1) * stride + (c + 1)]) bottom = true;
            else if (r + 2 <= maxR && vWalls[(r + 2) * stride + c]) bottom = true;
        }
        // Middle intersection connectivity
        bool middle = false;
        if (c >= 1 && hWalls[r * stride + (c - 1)]) middle = true;
        else if (c < maxC && hWalls[r * stride + (c + 1)]) middle = true;

        return (top && bottom) || (bottom && middle) || (middle && top);
    }
}

// ============================================================================
// EXACT NEMESIS PROBABLE WALL STENCILS (from game.js: setWallsBesidePawn &
// adjustProbableValidNextWallForAfterPlaceHorizontal/VerticalWall)
// ============================================================================
static inline bool isPawnBesideWallNemesis(int r, int c, int o, int pR, int pC) {
    if (o == 0) {
        // Horizontal wall beside pawn: rows [pR-1, pR], cols [pC-2 .. pC+1]
        if (r == pR - 1 || r == pR) {
            if (c >= pC - 2 && c <= pC + 1) return true;
        }
    } else {
        // Vertical wall beside pawn: rows [pR-2 .. pR+1], cols [pC-1, pC]
        if (c == pC - 1 || c == pC) {
            if (r >= pR - 2 && r <= pR + 1) return true;
        }
    }
    return false;
}

static inline bool isWallChainExtensionNemesis(int r, int c, int o) {
    if (totalWallsOnBoard == 0) return false;
    int stride = B_COLS - 1;
    int maxR = B_ROWS - 2;
    int maxC = B_COLS - 2;

    if (o == 0) {
        // Check if this horizontal wall is triggered by an existing H or V wall
        // 1. Triggered by existing Horizontal wall at (r, c +/- 2) or (r, c +/- 3) [1-cell door gap!]
        if (c >= 2 && hWalls[r * stride + (c - 2)]) return true;
        if (c + 2 <= maxC && hWalls[r * stride + (c + 2)]) return true;
        if (c >= 3 && hWalls[r * stride + (c - 3)]) return true;
        if (c + 3 <= maxC && hWalls[r * stride + (c + 3)]) return true;

        // 2. Triggered by existing Vertical wall at dr in [-2..2], dc in [-1..1]
        for (int dr = -2; dr <= 2; dr++) {
            int nr = r + dr;
            if (nr < 0 || nr > maxR) continue;
            for (int dc = -1; dc <= 1; dc++) {
                int nc = c + dc;
                if (nc >= 0 && nc <= maxC && vWalls[nr * stride + nc]) return true;
            }
        }
    } else {
        // Check if this vertical wall is triggered by an existing V or H wall
        // 1. Triggered by existing Vertical wall at (r +/- 2, c) or (r +/- 3, c) [1-cell door gap!]
        if (r >= 2 && vWalls[(r - 2) * stride + c]) return true;
        if (r + 2 <= maxR && vWalls[(r + 2) * stride + c]) return true;
        if (r >= 3 && vWalls[(r - 3) * stride + c]) return true;
        if (r + 3 <= maxR && vWalls[(r + 3) * stride + c]) return true;

        // 2. Triggered by existing Horizontal wall at dr in [-1..1], dc in [-2..2]
        for (int dr = -1; dr <= 1; dr++) {
            int nr = r + dr;
            if (nr < 0 || nr > maxR) continue;
            for (int dc = -2; dc <= 2; dc++) {
                int nc = c + dc;
                if (nc >= 0 && nc <= maxC && hWalls[nr * stride + nc]) return true;
            }
        }
    }
    return false;
}

static inline bool isNemesisProbableWall(int r, int c, int o, int pR, int pC, int eR, int eC) {
    int maxC = B_COLS - 2;
    // 1. Beside opponent pawn or own pawn (exact setWallsBesidePawn stencil)
    if (isPawnBesideWallNemesis(r, c, o, eR, eC)) return true;
    if (isPawnBesideWallNemesis(r, c, o, pR, pC)) return true;

    // 2. Leftmost and rightmost horizontal walls (c == 0 or c == maxC)
    if (o == 0 && (c == 0 || c == maxC)) return true;

    // 3. Exact Nemesis wall-chain & gap-1 door extensions
    if (isWallChainExtensionNemesis(r, c, o)) return true;

    return false;
}

static int16_t bfsQ[256];

static void runReverseGoalBfs(int goalRow, PathMetrics* outMetrics) {
    int total = B_ROWS * B_COLS;
    for (int i = 0; i < total; i++) {
        outMetrics[i] = {-1, 0, 0, 0};
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
        outMetrics[i] = {-1, 0, 0, 0};
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

static inline int fastLog2Ways(int16_t ways) {
    if (ways <= 1) return 0;
    if (ways <= 2) return 1;
    if (ways <= 4) return 2;
    if (ways <= 8) return 3;
    if (ways <= 16) return 4;
    if (ways <= 32) return 5;
    return 6;
}

// ============================================================================
// ANTI-NEMESIS CAGE PROBE (2-WALL POCKET & TRAP DETECTOR)
// ============================================================================
struct CageProbeResult {
    int maxDelta1;
    int maxDelta2;
    uint16_t bestW1;
    uint16_t bestW2;
};

static CageProbeResult probePlayerCage(int pR, int pC, int pGoal, int oppWallsLeft, int myWallsLeft) {
    CageProbeResult res = {0, 0, 0, 0};
    if (oppWallsLeft <= 0) return res;

    const DistCacheEntry& curDc = getCachedDistMaps();
    int pIdx = pR * B_COLS + pC;
    int baseD = (pGoal == 0) ? curDc.me[pIdx].dist : curDc.opp[pIdx].dist;
    if (baseD <= 0) return res;

    uint16_t candW1[64];
    int nCand1 = 0;

    int minR = max(0, pR - 3), maxR = min(B_ROWS - 2, pR + 3);
    int minC = max(0, pC - 3), maxC = min(B_COLS - 2, pC + 3);

    for (int r = minR; r <= maxR; r++) {
        for (int c = minC; c <= maxC; c++) {
            for (int o = 0; o < 2; o++) {
                if (!wallGeometryLegal(r, c, o)) continue;
                candW1[nCand1++] = packMove16(WALL, r, c, o);
                if (nCand1 >= 64) goto cand1_done;
            }
        }
    }
cand1_done:

    struct W1Score {
        uint16_t code;
        int delta1;
        int exitDrop;
    } scoredW1[64];
    int nScored = 0;
    int baseExits = (pGoal == 0) ? curDc.me[pIdx].exits : curDc.opp[pIdx].exits;

    for (int i = 0; i < nCand1; i++) {
        uint8_t t, r, c, o;
        unpackMove16(candW1[i], t, r, c, o);
        placeWallInternal(r, c, o);
        const DistCacheEntry& dc1 = getCachedDistMaps();
        int d1 = (pGoal == 0) ? dc1.me[pIdx].dist : dc1.opp[pIdx].dist;
        int ex1 = (pGoal == 0) ? dc1.me[pIdx].exits : dc1.opp[pIdx].exits;
        int dOppCheck = (pGoal == 0) ? dc1.opp[oppR * B_COLS + oppC].dist : dc1.me[myR * B_COLS + myC].dist;
        removeWallInternal(r, c, o);

        if (d1 < 0 || dOppCheck < 0) continue;
        int delta1 = d1 - baseD;
        if (delta1 > res.maxDelta1) {
            res.maxDelta1 = delta1;
            res.bestW1 = candW1[i];
        }
        scoredW1[nScored++] = {candW1[i], delta1, baseExits - ex1};
    }

    if (oppWallsLeft < 2) return res;

    sort(scoredW1, scoredW1 + nScored, [](const W1Score& a, const W1Score& b) {
        return (a.delta1 * 4 + a.exitDrop * 3) > (b.delta1 * 4 + b.exitDrop * 3);
    });

    int checkK = min(10, nScored);
    for (int k = 0; k < checkK; k++) {
        uint8_t t1, r1, c1, o1;
        unpackMove16(scoredW1[k].code, t1, r1, c1, o1);
        placeWallInternal(r1, c1, o1);

        int minR2 = max(0, r1 - 3), maxR2 = min(B_ROWS - 2, r1 + 3);
        int minC2 = max(0, c1 - 3), maxC2 = min(B_COLS - 2, c1 + 3);

        for (int r2 = minR2; r2 <= maxR2; r2++) {
            for (int c2 = minC2; c2 <= maxC2; c2++) {
                for (int o2 = 0; o2 < 2; o2++) {
                    if (!wallGeometryLegal(r2, c2, o2)) continue;
                    placeWallInternal(r2, c2, o2);
                    const DistCacheEntry& dc2 = getCachedDistMaps();
                    int d2 = (pGoal == 0) ? dc2.me[pIdx].dist : dc2.opp[pIdx].dist;
                    int dOpp2 = (pGoal == 0) ? dc2.opp[oppR * B_COLS + oppC].dist : dc2.me[myR * B_COLS + myC].dist;
                    removeWallInternal(r2, c2, o2);

                    if (d2 < 0 || dOpp2 < 0) continue;
                    int delta2 = d2 - baseD;
                    if (delta2 > res.maxDelta2) {
                        res.maxDelta2 = delta2;
                        res.bestW1 = scoredW1[k].code;
                        res.bestW2 = packMove16(WALL, r2, c2, o2);
                    }
                }
            }
        }
        removeWallInternal(r1, c1, o1);
    }
    return res;
}

static int evaluate2P(bool sideToMoveIsMe) {
    const EvalParams& P = (GAME_MODE == 1) ? PARAMS_RACE : PARAMS_DUEL;
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

    if (myWalls == 0 && oppWalls == 0) {
        int diff = (oppM.dist - myM.dist);
        int score = diff * P.tempoPerStep + (sideToMoveIsMe ? P.turnAdvantage : -P.turnAdvantage);
        if (myM.dist < oppM.dist || (myM.dist == oppM.dist && sideToMoveIsMe)) {
            score += 25000;
        } else {
            score -= 25000;
        }
        return sideToMoveIsMe ? score : -score;
    }

    int32_t score = (oppM.dist - myM.dist) * P.tempoPerStep + (sideToMoveIsMe ? P.turnAdvantage : -P.turnAdvantage);

    int minDist = min((int)myM.dist, (int)oppM.dist);
    int mwClamped = min(15, max(0, myWalls));
    int owClamped = min(15, max(0, oppWalls));
    int32_t rawWallDiff = WALL_MATERIAL_TABLE[mwClamped] - WALL_MATERIAL_TABLE[owClamped];

    if (minDist <= 2) rawWallDiff = (rawWallDiff * 45) / 100;
    else if (minDist <= 4) rawWallDiff = (rawWallDiff * 72) / 100;
    score += rawWallDiff;

    int myFlex = fastLog2Ways(myM.ways) * P.waysWeight + myM.exits * P.exitWeight;
    int oppFlex = fastLog2Ways(oppM.ways) * P.waysWeight + oppM.exits * P.exitWeight;
    score += (myFlex - oppFlex);

    if (oppM.exits == 1 && myWalls > 0) score += P.corridorTrapBonus;
    if (myM.exits == 1 && oppWalls > 0) score -= P.corridorTrapBonus;

    int manhattan = abs(myR - oppR) + abs(myC - oppC);
    if (manhattan == 1) {
        int stepBuf[8];
        if (sideToMoveIsMe) {
            int n = generatePawnSteps2P(myR, myC, oppR, oppC, stepBuf);
            for (int i = 0; i < n; i++) {
                if (dc.me[stepBuf[i]].dist <= myM.dist - 2) { score += P.oppositionBonus; break; }
            }
        } else {
            int n = generatePawnSteps2P(oppR, oppC, myR, myC, stepBuf);
            for (int i = 0; i < n; i++) {
                if (dc.opp[stepBuf[i]].dist <= oppM.dist - 2) { score -= P.oppositionBonus; break; }
            }
        }
    }

    int myCenter = 4 - abs(myC - 4);
    int oppCenter = 4 - abs(oppC - 4);
    score += (myCenter - oppCenter) * P.centerWeight;

    if (oppWalls >= 2) {
        CageProbeResult oppThreat = probePlayerCage(myR, myC, 0, oppWalls, myWalls);
        if (oppThreat.maxDelta2 >= 3) {
            int netThreat = (oppThreat.maxDelta2 - 2) * P.cageThreatWeight;
            score -= netThreat;
        }
    }
    if (myWalls >= 2) {
        CageProbeResult myAttack = probePlayerCage(oppR, oppC, oppGoal, myWalls, oppWalls);
        if (myAttack.maxDelta2 >= 3) {
            int netAttack = (myAttack.maxDelta2 - 2) * P.cageThreatWeight;
            score += netAttack;
        }
    }

    if (minDist <= 3) {
        score += (oppM.dist - myM.dist) * 550;
    }

    return sideToMoveIsMe ? score : -score;
}

static int generateMoves2P(Move* outMoves, bool isMe, uint16_t ttBest, uint16_t prevMove, int ply, bool qSearchOnly) {
    int pR = isMe ? myR : oppR;
    int pC = isMe ? myC : oppC;
    int eR = isMe ? oppR : myR;
    int eC = isMe ? oppC : myC;
    int pWalls = isMe ? myWalls : oppWalls;
    int eWalls = isMe ? oppWalls : myWalls;
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

        if (eWalls == 0 && pWalls == 0 && stepGain < 1 && count > 0) continue;

        if (qSearchOnly) {
            bool isJump = (stepGain >= 2) || (abs(pR - eR) + abs(pC - eC) == 1 && stepGain >= 1);
            bool isWinningThreat = (newD <= 1 && curP > 1);
            if (!isJump && !isWinningThreat) continue;
        }

        int32_t ord = stepGain * 16000 + pMap[cell].exits * 400 + historyTable[sideIdx][packed & 1023];
        if (packed == ttBest) ord += 60000000;
        if (packed == counterMove) ord += 15000;
        if (stepGain >= 2) ord += 18000;

        outMoves[count++] = {STEP, (uint8_t)sr, (uint8_t)sc, 0, ord};
    }

    if (pWalls <= 0) {
        sort(outMoves, outMoves + count, [](const Move& a, const Move& b) {
            return a.orderScore > b.orderScore;
        });
        return count;
    }

    Move wallBuf[256];
    int wCount = 0;
    int maxR = B_ROWS - 2;
    int maxC = B_COLS - 2;

    uint16_t cageInitiator = 0;
    if (pWalls >= 2) {
        CageProbeResult attackProbe = probePlayerCage(eR, eC, isMe ? (GAME_MODE == 1 ? 0 : B_ROWS - 1) : 0, pWalls, eWalls);
        if (attackProbe.maxDelta2 >= 3) {
            cageInitiator = attackProbe.bestW1;
        }
    }

    for (int r = 0; r <= maxR; r++) {
        for (int c = 0; c <= maxC; c++) {
            int idxTL = r * B_COLS + c;
            int dTL = eMap[idxTL].dist;
            int dTR = eMap[idxTL + 1].dist;
            int dBL = eMap[idxTL + B_COLS].dist;
            int dBR = eMap[idxTL + B_COLS + 1].dist;

            for (int o = 0; o < 2; o++) {
                if (!wallGeometryLegal(r, c, o)) continue;

                // Exact Nemesis shortest-path DAG edge-cutter check
                bool cutsShortest = false;
                if (o == 0) {
                    cutsShortest = (abs(dTL - dBL) == 1 && min(dTL, dBL) < curE) ||
                                   (abs(dTR - dBR) == 1 && min(dTR, dBR) < curE);
                } else {
                    cutsShortest = (abs(dTL - dTR) == 1 && min(dTL, dTR) < curE) ||
                                   (abs(dBL - dBR) == 1 && min(dBL, dBR) < curE);
                }

                uint16_t packed = packMove16(WALL, r, c, o);
                bool isCageW = (packed == cageInitiator);
                bool probable = isNemesisProbableWall(r, c, o, pR, pC, eR, eC);

                if (!cutsShortest && !probable && !isCageW) continue;

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

                // Nemesis Endgame Rule: when opponent has 0 walls, only place walls that interrupt opponent's path
                if (eWalls == 0 && eGain <= 0 && !isCageW) continue;

                if (qSearchOnly) {
                    bool forcing = (net >= 2) || (curE <= 3 && net >= 1 && pLoss == 0) || (net >= 1 && newEExits == 1 && exitDrop >= 1);
                    if (!forcing && !isCageW) continue;
                } else {
                    if (totalWallsOnBoard == 0 && curE >= 7 && net <= 1 && !isCageW) continue;
                    if (net < 0 && exitDrop <= 0 && !isCageW) continue;
                    if (net == 0 && exitDrop <= 0 && waysDrop <= 0 && !isCageW) continue;
                }

                int32_t ord = net * 10500 + eGain * 3500 + exitDrop * 3200 + (waysDrop > 0 ? 1500 : -1200) + historyTable[sideIdx][packed & 1023];

                if (newEExits == 1 && curEExits > 1) ord += 3600;
                if (isCageW) ord += 48000;

                if (packed == ttBest) ord += 60000000;
                if (packed == counterMove) ord += 15000;
                if (killerMoves[ply][0] == packed || killerMoves[ply][1] == packed) ord += 12000;

                if (GAME_MODE == 1) {
                    if (o == 1 && abs(c - eC) <= 1 && abs(r - eR) <= 2) ord += 1600;
                    if (pLoss > 0) ord -= pLoss * 3800;
                } else {
                    if (net >= 2 && pLoss == 0) ord += 6500;
                }

                wallBuf[wCount++] = {WALL, (uint8_t)r, (uint8_t)c, (uint8_t)o, ord};
            }
        }
    }

    sort(wallBuf, wallBuf + wCount, [](const Move& a, const Move& b) {
        return a.orderScore > b.orderScore;
    });

    int limit = qSearchOnly ? 6 : (ply == 0 ? 36 : (ply <= 2 ? 18 : 12));
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
    if (qply >= 5 || ply >= 60) return alpha;

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

        int extension = 0;
        if (ply <= 4) {
            CageProbeResult threat = probePlayerCage(sideToMoveIsMe ? myR : oppR,
                                                     sideToMoveIsMe ? myC : oppC,
                                                     sideToMoveIsMe ? 0 : oppGoal,
                                                     sideToMoveIsMe ? oppWalls : myWalls,
                                                     sideToMoveIsMe ? myWalls : oppWalls);
            if (threat.maxDelta2 >= 4) {
                extension = 1;
            }
        }

        int score;
        if (i == 0) {
            score = -pvs2P(depth - 1 + extension, ply + 1, -beta, -alpha, !sideToMoveIsMe, mCode);
        } else {
            int reduction = 0;
            if (depth >= 3 && i >= 5 && m.type == WALL && m.orderScore < 20000 && extension == 0) {
                reduction = (depth >= 6 && i >= 10) ? 2 : 1;
            }
            score = -pvs2P(depth - 1 - reduction, ply + 1, -alpha - 1, -alpha, !sideToMoveIsMe, mCode);
            if (!searchAborted && score > alpha && reduction > 0) {
                score = -pvs2P(depth - 1, ply + 1, -alpha - 1, -alpha, !sideToMoveIsMe, mCode);
            }
            if (!searchAborted && score > alpha && score < beta) {
                score = -pvs2P(depth - 1 + extension, ply + 1, -beta, -alpha, !sideToMoveIsMe, mCode);
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
// PARANOID ALPHA-BETA FOR 4-PLAYER QUAD (11x11)
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

static int evaluateQuadParanoid() {
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
                if (pIdx == 0 && net < 1 && bestTargetD > 2) continue;

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

static int quadParanoidSearch(int depth, int ply, int pIdx, int alpha, int beta) {
    if ((++nodesSearched & 63) == 0 && nowMs() >= searchDeadline) {
        searchAborted = true;
        return 0;
    }

    if (quadP[0].r == 5 && quadP[0].c == 5) return 100000 + depth;
    for (int i = 1; i < 4; i++) {
        if (quadP[i].active && quadP[i].r == 5 && quadP[i].c == 5) return -100000 - depth;
    }

    if (depth <= 0 || ply >= 24) return evaluateQuadParanoid();

    int nextP = (pIdx + 1) % 4;
    while (!quadP[nextP].active && nextP != pIdx) {
        nextP = (nextP + 1) % 4;
    }

    Move moves[32];
    int nMoves = generateQuadMoves(pIdx, moves, false);
    if (nMoves == 0) return evaluateQuadParanoid();

    bool isMax = (pIdx == 0);
    int bestVal = isMax ? -200000 : 200000;
    int limit = isMax ? min(nMoves, 14) : min(nMoves, 8);
    QuadPlayer& cur = quadP[pIdx];

    for (int i = 0; i < limit; i++) {
        const Move& m = moves[i];
        int sr = cur.r, sc = cur.c;
        if (m.type == STEP) {
            cur.r = m.r; cur.c = m.c;
        } else {
            placeWallInternal(m.r, m.c, m.o);
            cur.walls--;
        }

        int val = quadParanoidSearch(depth - 1, ply + 1, nextP, alpha, beta);

        if (m.type == STEP) {
            cur.r = sr; cur.c = sc;
        } else {
            removeWallInternal(m.r, m.c, m.o);
            cur.walls++;
        }

        if (searchAborted) return 0;

        if (isMax) {
            if (val > bestVal) bestVal = val;
            if (bestVal > alpha) alpha = bestVal;
            if (alpha >= beta) break;
        } else {
            if (val < bestVal) bestVal = val;
            if (bestVal < beta) beta = bestVal;
            if (beta <= alpha) break;
        }
    }
    return bestVal;
}

extern "C" {

EXPORT_FN int getNodesSearched() {
    return (int)nodesSearched;
}

EXPORT_FN int getCompletedDepth() {
    return completedDepthGlobal;
}

EXPORT_FN int search(int mode, int rows, int cols,
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

        for (int d = 1; d <= min(maxDepth, 8); d++) {
            if (nowMs() >= searchDeadline) break;
            searchAborted = false;
            Move iterBest = bestMove;
            int iterScore = -200000;

            for (int i = 0; i < nRoot; i++) {
                const Move& m = rootMoves[i];
                int sr = quadP[0].r, sc = quadP[0].c;
                if (m.type == STEP) { quadP[0].r = m.r; quadP[0].c = m.c; }
                else { placeWallInternal(m.r, m.c, m.o); quadP[0].walls--; }

                int scVal = quadParanoidSearch(d - 1, 1, 1, iterScore, 200000);

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

    if (myWalls == 0 && oppWalls == 0) {
        completedDepthGlobal = 1;
        return packMove16(bestMove.type, bestMove.r, bestMove.c, bestMove.o);
    }

    int prevScore = evaluate2P(true);

    for (int d = 1; d <= maxDepth; d++) {
        if (nowMs() >= searchDeadline) break;
        searchAborted = false;

        int delta = 700;
        int alpha = (d >= 3) ? max(-200000, prevScore - delta) : -200000;
        int beta  = (d >= 3) ? min(200000, prevScore + delta)  : 200000;

        Move iterBest = bestMove;
        int iterBestScore = -200000;

        while (true) {
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

} // extern "C"
