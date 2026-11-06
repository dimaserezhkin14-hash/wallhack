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
// EXACT 1-TO-1 PORT OF NEMESIS (gorisanson/quoridor-ai v0.3)
// Algorithm: UCT Monte Carlo Tree Search (MCTS)
// - uctConst = 0.2 (exact v0.3 tuning)
// - 60,000 rollouts per move (Strong / Nemesis tier)
// - Final move selection: Robust Child (max visit count N, NOT max winrate)
// - Rollout policy: 70% shortest-path pawn step, 30% probable wall (or backward
//   step penalty if 0 walls left)
// - Two-point topological connectivity filter + Probable Wall Stencil
// - Opening book for first 6 plies + Exact 0-wall race solver
// ============================================================================

enum MoveType : uint8_t { STEP = 0, WALL = 1 };

struct Move {
    uint8_t type;    // 0 = step, 1 = wall
    uint8_t r, c, o; // o: 0 = h, 1 = v
};

static inline uint16_t packMove16(uint8_t type, uint8_t r, uint8_t c, uint8_t o) {
    return (uint16_t)((type & 1) | ((o & 1) << 1) | ((r & 15) << 2) | ((c & 15) << 6));
}

static inline Move unpackMove16(uint16_t code) {
    return {
        (uint8_t)(code & 1),
        (uint8_t)((code >> 2) & 15),
        (uint8_t)((code >> 6) & 15),
        (uint8_t)((code >> 1) & 1)
    };
}

static int B_ROWS = 9;
static int B_COLS = 9;
static int GAME_MODE = 0; // 0 = Duel 9x9, 1 = Race 9x13, 2 = Quad 11x11

static uint32_t rngState = 0x13579BDFU;
static inline uint32_t fastRand() {
    uint32_t x = rngState;
    x ^= x << 13;
    x ^= x >> 17;
    x ^= x << 5;
    return rngState = x;
}
static inline double fastRand01() {
    return (fastRand() & 0xFFFFFF) / 16777216.0;
}

struct BoardState {
    uint8_t hWalls[169];
    uint8_t vWalls[169];
    int pR[2], pC[2], pWalls[2];
    int turn; // 0 = me (goal 0), 1 = opp (goal B_ROWS-1 or 0 in race)
    int totalWalls;
};

static inline int goalRowOf(int side) {
    if (GAME_MODE == 1) return 0;
    return (side == 0) ? 0 : (B_ROWS - 1);
}

static inline bool canUpB(const BoardState& b, int r, int c) {
    if (r <= 0) return false;
    int wC = B_COLS - 1;
    int base = (r - 1) * wC;
    return (c >= wC || b.hWalls[base + c] == 0) && (c <= 0 || b.hWalls[base + c - 1] == 0);
}
static inline bool canDownB(const BoardState& b, int r, int c) {
    if (r >= B_ROWS - 1) return false;
    int wC = B_COLS - 1;
    int base = r * wC;
    return (c >= wC || b.hWalls[base + c] == 0) && (c <= 0 || b.hWalls[base + c - 1] == 0);
}
static inline bool canLeftB(const BoardState& b, int r, int c) {
    if (c <= 0) return false;
    int wC = B_COLS - 1;
    return (r >= B_ROWS - 1 || b.vWalls[r * wC + c - 1] == 0) && (r <= 0 || b.vWalls[(r - 1) * wC + c - 1] == 0);
}
static inline bool canRightB(const BoardState& b, int r, int c) {
    int wC = B_COLS - 1;
    if (c >= wC) return false;
    return (r >= B_ROWS - 1 || b.vWalls[r * wC + c] == 0) && (r <= 0 || b.vWalls[(r - 1) * wC + c] == 0);
}

static inline bool canStepDirB(const BoardState& b, int r, int c, int d) {
    if (d == 0) return canUpB(b, r, c);
    if (d == 1) return canDownB(b, r, c);
    if (d == 2) return canLeftB(b, r, c);
    return canRightB(b, r, c);
}

static const int DR[4] = {-1, 1, 0, 0};
static const int DC[4] = {0, 0, -1, 1};

static inline bool wallGeometryLegalB(const BoardState& b, int r, int c, int o) {
    int maxR = B_ROWS - 2;
    int maxC = B_COLS - 2;
    if (r < 0 || r > maxR || c < 0 || c > maxC) return false;
    int stride = B_COLS - 1;
    int idx = r * stride + c;
    if (o == 0) {
        if (b.hWalls[idx] || b.vWalls[idx]) return false;
        if ((c > 0 && b.hWalls[idx - 1]) || (c < maxC && b.hWalls[idx + 1])) return false;
        return true;
    } else {
        if (b.vWalls[idx] || b.hWalls[idx]) return false;
        if ((r > 0 && b.vWalls[idx - stride]) || (r < maxR && b.vWalls[idx + stride])) return false;
        return true;
    }
}

// Exact testIfConnectedOnTwoPoints from gorisanson/quoridor-ai game.js
static inline bool isConnectedOnTwoPointsB(const BoardState& b, int r, int c, int o) {
    int stride = B_COLS - 1;
    int maxR = B_ROWS - 2;
    int maxC = B_COLS - 2;

    if (o == 0) {
        bool left = (c == 0);
        if (!left && c >= 1) {
            if (b.vWalls[r * stride + (c - 1)] ||
                (r >= 1 && b.vWalls[(r - 1) * stride + (c - 1)]) ||
                (r < maxR && b.vWalls[(r + 1) * stride + (c - 1)]) ||
                (c >= 2 && b.hWalls[r * stride + (c - 2)])) left = true;
        }
        bool right = (c == maxC);
        if (!right && c < maxC) {
            if (b.vWalls[r * stride + (c + 1)] ||
                (r >= 1 && b.vWalls[(r - 1) * stride + (c + 1)]) ||
                (r < maxR && b.vWalls[(r + 1) * stride + (c + 1)]) ||
                (c + 2 <= maxC && b.hWalls[r * stride + (c + 2)])) right = true;
        }
        bool middle = (r >= 1 && b.vWalls[(r - 1) * stride + c]) ||
                      (r < maxR && b.vWalls[(r + 1) * stride + c]);
        return (left && right) || (right && middle) || (middle && left);
    } else {
        bool top = (r == 0);
        if (!top && r >= 1) {
            if (b.hWalls[(r - 1) * stride + c] ||
                (c >= 1 && b.hWalls[(r - 1) * stride + (c - 1)]) ||
                (c < maxC && b.hWalls[(r - 1) * stride + (c + 1)]) ||
                (r >= 2 && b.vWalls[(r - 2) * stride + c])) top = true;
        }
        bool bottom = (r == maxR);
        if (!bottom && r < maxR) {
            if (b.hWalls[(r + 1) * stride + c] ||
                (c >= 1 && b.hWalls[(r + 1) * stride + (c - 1)]) ||
                (c < maxC && b.hWalls[(r + 1) * stride + (c + 1)]) ||
                (r + 2 <= maxR && b.vWalls[(r + 2) * stride + c])) bottom = true;
        }
        bool middle = (c >= 1 && b.hWalls[r * stride + (c - 1)]) ||
                      (c < maxC && b.hWalls[r * stride + (c + 1)]);
        return (top && bottom) || (bottom && middle) || (middle && top);
    }
}

static int16_t bfsQ[256];

static void computeDistToGoal(const BoardState& b, int goalRow, int8_t* dist) {
    int total = B_ROWS * B_COLS;
    memset(dist, -1, total);
    int head = 0, tail = 0;
    int base = goalRow * B_COLS;
    for (int c = 0; c < B_COLS; c++) {
        dist[base + c] = 0;
        bfsQ[tail++] = base + c;
    }
    while (head < tail) {
        int idx = bfsQ[head++];
        int r = idx / B_COLS;
        int c = idx - r * B_COLS;
        int8_t nd = dist[idx] + 1;
        if (canUpB(b, r, c) && dist[idx - B_COLS] == -1) { dist[idx - B_COLS] = nd; bfsQ[tail++] = idx - B_COLS; }
        if (canDownB(b, r, c) && dist[idx + B_COLS] == -1) { dist[idx + B_COLS] = nd; bfsQ[tail++] = idx + B_COLS; }
        if (canLeftB(b, r, c) && dist[idx - 1] == -1) { dist[idx - 1] = nd; bfsQ[tail++] = idx - 1; }
        if (canRightB(b, r, c) && dist[idx + 1] == -1) { dist[idx + 1] = nd; bfsQ[tail++] = idx + 1; }
    }
}

static bool hasPathToGoal(const BoardState& b, int startR, int startC, int goalRow) {
    uint8_t vis[169];
    memset(vis, 0, B_ROWS * B_COLS);
    int head = 0, tail = 0;
    int startIdx = startR * B_COLS + startC;
    vis[startIdx] = 1;
    bfsQ[tail++] = startIdx;
    while (head < tail) {
        int idx = bfsQ[head++];
        int r = idx / B_COLS;
        if (r == goalRow) return true;
        int c = idx - r * B_COLS;
        if (canUpB(b, r, c) && !vis[idx - B_COLS]) { vis[idx - B_COLS] = 1; bfsQ[tail++] = idx - B_COLS; }
        if (canDownB(b, r, c) && !vis[idx + B_COLS]) { vis[idx + B_COLS] = 1; bfsQ[tail++] = idx + B_COLS; }
        if (canLeftB(b, r, c) && !vis[idx - 1]) { vis[idx - 1] = 1; bfsQ[tail++] = idx - 1; }
        if (canRightB(b, r, c) && !vis[idx + 1]) { vis[idx + 1] = 1; bfsQ[tail++] = idx + 1; }
    }
    return false;
}

static inline bool isWallLegalFull(BoardState& b, int r, int c, int o) {
    if (!wallGeometryLegalB(b, r, c, o)) return false;
    bool checkPaths = isConnectedOnTwoPointsB(b, r, c, o);
    if (!checkPaths) return true; // O(1) guarantee that paths remain open!

    int idx = r * (B_COLS - 1) + c;
    if (o == 0) b.hWalls[idx] = 1; else b.vWalls[idx] = 1;
    bool ok = hasPathToGoal(b, b.pR[0], b.pC[0], goalRowOf(0)) &&
              hasPathToGoal(b, b.pR[1], b.pC[1], goalRowOf(1));
    if (o == 0) b.hWalls[idx] = 0; else b.vWalls[idx] = 0;
    return ok;
}

// Exact Probable Next Walls from gorisanson/quoridor-ai
static inline bool isProbableWallNemesisB(const BoardState& b, int r, int c, int o) {
    int maxR = B_ROWS - 2, maxC = B_COLS - 2;
    int stride = B_COLS - 1;

    // 1. Near pawns (setWallsBesidePawn)
    for (int s = 0; s < 2; s++) {
        int pr = b.pR[s], pc = b.pC[s];
        if (o == 0) {
            if ((r == pr - 1 || r == pr) && c >= pc - 2 && c <= pc + 1) return true;
        } else {
            if ((c == pc - 1 || c == pc) && r >= pr - 2 && r <= pr + 1) return true;
        }
    }

    // 2. Leftmost or rightmost horizontal walls (after opening)
    if (b.totalWalls >= 2 && o == 0 && (c == 0 || c == maxC)) return true;

    // 3. Near already placed walls (including gap-1 doors col +/- 3, row +/- 3)
    if (b.totalWalls > 0) {
        if (o == 0) {
            if (c >= 2 && b.hWalls[r * stride + (c - 2)]) return true;
            if (c + 2 <= maxC && b.hWalls[r * stride + (c + 2)]) return true;
            if (c >= 3 && b.hWalls[r * stride + (c - 3)]) return true;
            if (c + 3 <= maxC && b.hWalls[r * stride + (c + 3)]) return true;
            for (int dr = -2; dr <= 2; dr++) {
                int nr = r + dr;
                if (nr < 0 || nr > maxR) continue;
                for (int dc = -1; dc <= 1; dc++) {
                    int nc = c + dc;
                    if (nc >= 0 && nc <= maxC && b.vWalls[nr * stride + nc]) return true;
                }
            }
        } else {
            if (r >= 2 && b.vWalls[(r - 2) * stride + c]) return true;
            if (r + 2 <= maxR && b.vWalls[(r + 2) * stride + c]) return true;
            if (r >= 3 && b.vWalls[(r - 3) * stride + c]) return true;
            if (r + 3 <= maxR && b.vWalls[(r + 3) * stride + c]) return true;
            for (int dr = -1; dr <= 1; dr++) {
                int nr = r + dr;
                if (nr < 0 || nr > maxR) continue;
                for (int dc = -2; dc <= 2; dc++) {
                    int nc = c + dc;
                    if (nc >= 0 && nc <= maxC && b.hWalls[nr * stride + nc]) return true;
                }
            }
        }
    }
    return false;
}

static int generatePawnStepsB(const BoardState& b, int side, int* outCells) {
    int pR = b.pR[side], pC = b.pC[side];
    int oR = b.pR[1 - side], oC = b.pC[1 - side];
    int cnt = 0;
    for (int d = 0; d < 4; d++) {
        if (!canStepDirB(b, pR, pC, d)) continue;
        int nr = pR + DR[d], nc = pC + DC[d];
        if (nr == oR && nc == oC) {
            if (canStepDirB(b, oR, oC, d)) {
                outCells[cnt++] = (oR + DR[d]) * B_COLS + (oC + DC[d]);
            } else {
                if (d < 2) {
                    if (canLeftB(b, oR, oC)) outCells[cnt++] = oR * B_COLS + (oC - 1);
                    if (canRightB(b, oR, oC)) outCells[cnt++] = oR * B_COLS + (oC + 1);
                } else {
                    if (canUpB(b, oR, oC)) outCells[cnt++] = (oR - 1) * B_COLS + oC;
                    if (canDownB(b, oR, oC)) outCells[cnt++] = (oR + 1) * B_COLS + oC;
                }
            }
        } else {
            outCells[cnt++] = nr * B_COLS + nc;
        }
    }
    return cnt;
}

static inline void applyMoveB(BoardState& b, uint16_t code) {
    Move m = unpackMove16(code);
    int s = b.turn;
    if (m.type == STEP) {
        b.pR[s] = m.r;
        b.pC[s] = m.c;
    } else {
        int idx = m.r * (B_COLS - 1) + m.c;
        if (m.o == 0) b.hWalls[idx] = 1; else b.vWalls[idx] = 1;
        b.pWalls[s]--;
        b.totalWalls++;
    }
    b.turn = 1 - s;
}

// ============================================================================
// MCTS NODE ARENA (PREALLOCATED FOR 60,000 SIMULATIONS)
// ============================================================================
struct MNode {
    int32_t parent;
    int32_t firstChild;
    uint16_t numChildren;
    uint16_t moveCode;
    uint8_t moverSide;      // side that made moveCode to reach this node
    uint8_t untriedCount;
    uint8_t isTerminal;     // 0 = no, 1 = side 0 won, 2 = side 1 won
    int32_t visits;
    double wins;            // wins from perspective of moverSide
};

static const int MAX_MCTS_NODES = 320000;
static MNode mctsArena[MAX_MCTS_NODES];
static int mctsNodeCount = 0;

// Expansion candidate buffer for current node being expanded
static int expandMovesForState(BoardState& b, uint16_t* outCodes) {
    int s = b.turn;
    int opp = 1 - s;
    int gMy = goalRowOf(s);
    int gOpp = goalRowOf(opp);

    int8_t dMy[169], dOpp[169];
    computeDistToGoal(b, gMy, dMy);
    computeDistToGoal(b, gOpp, dOpp);

    int curMyD = dMy[b.pR[s] * B_COLS + b.pC[s]];
    int curOppD = dOpp[b.pR[opp] * B_COLS + b.pC[opp]];

    int count = 0;
    int stepCells[8];
    int nSteps = generatePawnStepsB(b, s, stepCells);

    // Heuristic from gorisanson/quoridor-ai:
    // If opponent has no walls left, player moves pawn ONLY to one of the shortest paths!
    bool onlyShortestPawnSteps = (b.pWalls[opp] == 0);

    int bestStepD = 999;
    for (int i = 0; i < nSteps; i++) {
        int cell = stepCells[i];
        int sr = cell / B_COLS;
        if (sr == gMy) {
            outCodes[0] = packMove16(STEP, sr, cell % B_COLS, 0);
            return 1;
        }
        if (dMy[cell] >= 0 && dMy[cell] < bestStepD) bestStepD = dMy[cell];
    }

    for (int i = 0; i < nSteps; i++) {
        int cell = stepCells[i];
        if (onlyShortestPawnSteps && dMy[cell] > bestStepD) continue;
        outCodes[count++] = packMove16(STEP, cell / B_COLS, cell % B_COLS, 0);
    }

    if (b.pWalls[s] <= 0) return count;

    // If we are already strictly winning the race and opponent has 0 walls, don't waste walls
    if (b.pWalls[opp] == 0 && curMyD <= curOppD) return count;

    int maxR = B_ROWS - 2, maxC = B_COLS - 2;
    for (int r = 0; r <= maxR; r++) {
        for (int c = 0; c <= maxC; c++) {
            int idxTL = r * B_COLS + c;
            int dTL = dOpp[idxTL], dTR = dOpp[idxTL + 1];
            int dBL = dOpp[idxTL + B_COLS], dBR = dOpp[idxTL + B_COLS + 1];

            for (int o = 0; o < 2; o++) {
                if (!wallGeometryLegalB(b, r, c, o)) continue;

                // Check if wall cuts opponent's shortest path (getValidNextWallsDisturbPathOf)
                bool disturbsOpp = false;
                if (o == 0) {
                    disturbsOpp = (abs(dTL - dBL) == 1 && min(dTL, dBL) < curOppD) ||
                                  (abs(dTR - dBR) == 1 && min(dTR, dBR) < curOppD);
                } else {
                    disturbsOpp = (abs(dTL - dTR) == 1 && min(dTL, dTR) < curOppD) ||
                                  (abs(dBL - dBR) == 1 && min(dBL, dBR) < curOppD);
                }

                // Exact gorisanson heuristic: if opponent has 0 walls, ONLY place walls that disturb opponent's path
                if (b.pWalls[opp] == 0) {
                    if (!disturbsOpp) continue;
                } else {
                    if (!disturbsOpp && !isProbableWallNemesisB(b, r, c, o)) continue;
                }

                if (!isWallLegalFull(b, r, c, o)) continue;
                outCodes[count++] = packMove16(WALL, r, c, o);
            }
        }
    }
    return count;
}

// ============================================================================
// EXACT NEMESIS ROLLOUT SIMULATION (ai.js: rollout / simulation phase)
// - With probability A = 0.7: move pawn to one of the shortest paths.
// - With probability 1 - A = 0.3: place a probable next wall randomly if walls
//   left; otherwise move pawn backwards to give penalty for having 0 walls left!
// ============================================================================
static int simulateNemesisRollout(BoardState b) {
    int maxSimSteps = 120;
    int8_t dMap[169];

    for (int step = 0; step < maxSimSteps; step++) {
        if (b.pR[0] == goalRowOf(0)) return 0;
        if (b.pR[1] == goalRowOf(1)) return 1;

        // Fast exact termination when both players have 0 walls
        if (b.pWalls[0] == 0 && b.pWalls[1] == 0) {
            int8_t d0[169], d1[169];
            computeDistToGoal(b, goalRowOf(0), d0);
            computeDistToGoal(b, goalRowOf(1), d1);
            int dist0 = d0[b.pR[0] * B_COLS + b.pC[0]];
            int dist1 = d1[b.pR[1] * B_COLS + b.pC[1]];
            if (b.turn == 0) return (dist0 <= dist1) ? 0 : 1;
            else return (dist1 <= dist0) ? 1 : 0;
        }

        int s = b.turn;
        int gMy = goalRowOf(s);
        bool choosePawnMove = (fastRand01() < 0.70);

        if (choosePawnMove) {
            computeDistToGoal(b, gMy, dMap);
            int stepCells[8];
            int nSteps = generatePawnStepsB(b, s, stepCells);
            int bestD = 999;
            int bestCands[8], nBest = 0;
            for (int i = 0; i < nSteps; i++) {
                int cell = stepCells[i];
                int d = dMap[cell];
                if (d >= 0 && d < bestD) {
                    bestD = d;
                    bestCands[0] = cell;
                    nBest = 1;
                } else if (d == bestD) {
                    bestCands[nBest++] = cell;
                }
            }
            if (nBest > 0) {
                int chosen = bestCands[fastRand() % nBest];
                b.pR[s] = chosen / B_COLS;
                b.pC[s] = chosen % B_COLS;
                b.turn = 1 - s;
                continue;
            }
        }

        // Remaining 30% probability: try placing a probable wall if walls > 0
        if (b.pWalls[s] > 0) {
            uint16_t wallCands[128];
            int nW = 0;
            int maxR = B_ROWS - 2, maxC = B_COLS - 2;
            for (int r = 0; r <= maxR; r++) {
                for (int c = 0; c <= maxC; c++) {
                    for (int o = 0; o < 2; o++) {
                        if (wallGeometryLegalB(b, r, c, o) && isProbableWallNemesisB(b, r, c, o)) {
                            wallCands[nW++] = packMove16(WALL, r, c, o);
                        }
                    }
                }
            }
            // Try up to 6 random probable walls to find a legal one quickly
            bool placed = false;
            for (int tries = 0; tries < 6 && nW > 0; tries++) {
                int idx = fastRand() % nW;
                Move wm = unpackMove16(wallCands[idx]);
                if (isWallLegalFull(b, wm.r, wm.c, wm.o)) {
                    applyMoveB(b, wallCands[idx]);
                    placed = true;
                    break;
                }
                wallCands[idx] = wallCands[--nW];
            }
            if (placed) continue;
        } else {
            // Exact gorisanson penalty: 0 walls left on the 30% branch -> move pawn BACKWARDS
            computeDistToGoal(b, gMy, dMap);
            int stepCells[8];
            int nSteps = generatePawnStepsB(b, s, stepCells);
            int worstD = -1;
            int worstCell = -1;
            for (int i = 0; i < nSteps; i++) {
                int cell = stepCells[i];
                if (dMap[cell] > worstD) {
                    worstD = dMap[cell];
                    worstCell = cell;
                }
            }
            if (worstCell >= 0) {
                b.pR[s] = worstCell / B_COLS;
                b.pC[s] = worstCell % B_COLS;
                b.turn = 1 - s;
                continue;
            }
        }

        // Fallback: move pawn forward
        computeDistToGoal(b, gMy, dMap);
        int stepCells[8];
        int nSteps = generatePawnStepsB(b, s, stepCells);
        int bestD = 999, bestCell = stepCells[0];
        for (int i = 0; i < nSteps; i++) {
            int cell = stepCells[i];
            if (dMap[cell] >= 0 && dMap[cell] < bestD) {
                bestD = dMap[cell];
                bestCell = cell;
            }
        }
        b.pR[s] = bestCell / B_COLS;
        b.pC[s] = bestCell % B_COLS;
        b.turn = 1 - s;
    }

    int8_t d0[169], d1[169];
    computeDistToGoal(b, goalRowOf(0), d0);
    computeDistToGoal(b, goalRowOf(1), d1);
    int dist0 = d0[b.pR[0] * B_COLS + b.pC[0]];
    int dist1 = d1[b.pR[1] * B_COLS + b.pC[1]];
    return (dist0 <= dist1) ? 0 : 1;
}

static int32_t allocMNode(int32_t parent, uint16_t moveCode, uint8_t moverSide) {
    if (mctsNodeCount >= MAX_MCTS_NODES) return -1;
    int32_t idx = mctsNodeCount++;
    MNode& n = mctsArena[idx];
    n.parent = parent;
    n.firstChild = -1;
    n.numChildren = 0;
    n.moveCode = moveCode;
    n.moverSide = moverSide;
    n.untriedCount = 0;
    n.isTerminal = 0;
    n.visits = 0;
    n.wins = 0.0;
    return idx;
}

static void expandNodeChildren(int32_t nodeIdx, BoardState& b) {
    MNode& n = mctsArena[nodeIdx];
    if (b.pR[0] == goalRowOf(0)) { n.isTerminal = 1; return; }
    if (b.pR[1] == goalRowOf(1)) { n.isTerminal = 2; return; }

    uint16_t codes[160];
    int cnt = expandMovesForState(b, codes);
    if (cnt == 0 || mctsNodeCount + cnt >= MAX_MCTS_NODES) return;

    // Shuffle move order slightly to prevent deterministic tie bias (as in MCTS)
    for (int i = cnt - 1; i > 0; i--) {
        int j = fastRand() % (i + 1);
        swap(codes[i], codes[j]);
    }

    n.firstChild = mctsNodeCount;
    n.numChildren = (uint16_t)cnt;
    uint8_t mover = (uint8_t)b.turn;
    for (int i = 0; i < cnt; i++) {
        allocMNode(nodeIdx, codes[i], mover);
    }
}

// ============================================================================
// MAIN UCT MCTS SEARCH (60,000 ROLLOUTS, uctConst = 0.2, ROBUST CHILD)
// ============================================================================
static uint32_t totalSimulationsRun = 0;
static int completedDepthGlobal = 0;

static uint16_t runNemesisMCTS(const BoardState& rootState, int timeBudgetMs, int maxRollouts) {
    // 1. Immediate win check
    int stepCells[8];
    int nSteps = generatePawnStepsB(rootState, 0, stepCells);
    for (int i = 0; i < nSteps; i++) {
        int r = stepCells[i] / B_COLS, c = stepCells[i] % B_COLS;
        if (r == goalRowOf(0)) {
            totalSimulationsRun = 1;
            completedDepthGlobal = 1;
            return packMove16(STEP, r, c, 0);
        }
    }

    // 2. Exact 0-wall Endgame Solver (no MCTS needed when 0 walls remain)
    if (rootState.pWalls[0] == 0 && rootState.pWalls[1] == 0) {
        int8_t d0[169];
        computeDistToGoal(rootState, goalRowOf(0), d0);
        int bestD = 999, bestCell = stepCells[0];
        for (int i = 0; i < nSteps; i++) {
            int cell = stepCells[i];
            if (d0[cell] >= 0 && d0[cell] < bestD) {
                bestD = d0[cell];
                bestCell = cell;
            }
        }
        totalSimulationsRun = 1;
        completedDepthGlobal = 20;
        return packMove16(STEP, bestCell / B_COLS, bestCell % B_COLS, 0);
    }

    // 3. Opening Book (first 4 plies straight advancement if unobstructed, as in gorisanson)
    if (GAME_MODE == 0 && rootState.totalWalls == 0 && rootState.pR[0] >= 6 && rootState.pC[0] == 4) {
        if (canUpB(rootState, rootState.pR[0], rootState.pC[0]) &&
            !(rootState.pR[1] == rootState.pR[0] - 1 && rootState.pC[1] == 4)) {
            totalSimulationsRun = 1;
            completedDepthGlobal = 10;
            return packMove16(STEP, rootState.pR[0] - 1, 4, 0);
        }
    }

    mctsNodeCount = 0;
    BoardState rootCopy = rootState;
    int32_t rootIdx = allocMNode(-1, 0, 1);
    expandNodeChildren(rootIdx, rootCopy);

    if (mctsArena[rootIdx].numChildren == 0) {
        return packMove16(STEP, stepCells[0] / B_COLS, stepCells[0] % B_COLS, 0);
    }
    if (mctsArena[rootIdx].numChildren == 1) {
        return mctsArena[mctsArena[rootIdx].firstChild].moveCode;
    }

    const double UCT_CONST = 0.2; // Exact v0.3 uctConst from gorisanson/quoridor-ai
    int64_t deadline = chrono::duration_cast<chrono::milliseconds>(
        chrono::steady_clock::now().time_since_epoch()
    ).count() + timeBudgetMs;

    int sims = 0;
    int maxDepthReached = 1;

    for (; sims < maxRollouts; sims++) {
        if ((sims & 127) == 0) {
            int64_t now = chrono::duration_cast<chrono::milliseconds>(
                chrono::steady_clock::now().time_since_epoch()
            ).count();
            if (now >= deadline) break;
        }

        BoardState simState = rootState;
        int32_t curIdx = rootIdx;
        int depth = 0;

        // Phase 1: Selection (UCT with uctConst = 0.2)
        while (true) {
            MNode& cur = mctsArena[curIdx];
            if (cur.isTerminal != 0 || cur.numChildren == 0) break;

            int32_t unvisitedChild = -1;
            int32_t bestChild = cur.firstChild;
            double bestUCT = -1e18;
            double logParent = log((double)max(1, cur.visits));

            for (int i = 0; i < cur.numChildren; i++) {
                int32_t cIdx = cur.firstChild + i;
                const MNode& ch = mctsArena[cIdx];
                if (ch.visits == 0) {
                    unvisitedChild = cIdx;
                    break;
                }
                double winRate = ch.wins / (double)ch.visits;
                double uct = winRate + UCT_CONST * sqrt(logParent / (double)ch.visits);
                if (uct > bestUCT) {
                    bestUCT = uct;
                    bestChild = cIdx;
                }
            }

            if (unvisitedChild != -1) {
                curIdx = unvisitedChild;
                applyMoveB(simState, mctsArena[curIdx].moveCode);
                depth++;
                break;
            }

            curIdx = bestChild;
            applyMoveB(simState, mctsArena[curIdx].moveCode);
            depth++;
        }

        if (depth > maxDepthReached) maxDepthReached = depth;

        // Phase 2: Expansion
        MNode& leaf = mctsArena[curIdx];
        if (leaf.visits > 0 && leaf.numChildren == 0 && leaf.isTerminal == 0) {
            expandNodeChildren(curIdx, simState);
            if (leaf.numChildren > 0) {
                curIdx = leaf.firstChild + (fastRand() % leaf.numChildren);
                applyMoveB(simState, mctsArena[curIdx].moveCode);
            }
        }

        // Phase 3: Simulation (Rollout)
        int winnerSide;
        if (mctsArena[curIdx].isTerminal == 1) winnerSide = 0;
        else if (mctsArena[curIdx].isTerminal == 2) winnerSide = 1;
        else winnerSide = simulateNemesisRollout(simState);

        // Phase 4: Backpropagation
        int32_t backIdx = curIdx;
        while (backIdx != -1) {
            MNode& bn = mctsArena[backIdx];
            bn.visits++;
            if (bn.moverSide == winnerSide) {
                bn.wins += 1.0;
            }
            backIdx = bn.parent;
        }
    }

    totalSimulationsRun = (uint32_t)sims;
    completedDepthGlobal = maxDepthReached;

    // Final Selection: ROBUST CHILD (child with highest visit count, tie-break by winrate)
    const MNode& root = mctsArena[rootIdx];
    int32_t bestChildIdx = root.firstChild;
    int32_t maxVisits = -1;
    double bestWR = -1.0;

    for (int i = 0; i < root.numChildren; i++) {
        int32_t cIdx = root.firstChild + i;
        const MNode& ch = mctsArena[cIdx];
        double wr = (ch.visits > 0) ? (ch.wins / ch.visits) : 0.0;
        if (ch.visits > maxVisits || (ch.visits == maxVisits && wr > bestWR)) {
            maxVisits = ch.visits;
            bestWR = wr;
            bestChildIdx = cIdx;
        }
    }

    return mctsArena[bestChildIdx].moveCode;
}

// ============================================================================
// QUAD 4-PLAYER MODE (11x11) SUPPORT
// ============================================================================
struct QuadPlayer {
    int r, c, walls;
    bool active;
};
static QuadPlayer quadP[4];

static uint16_t searchQuadSimple(const BoardState& b) {
    int8_t dist[169];
    memset(dist, -1, sizeof(dist));
    int head = 0, tail = 0;
    int center = 5 * 11 + 5;
    dist[center] = 0;
    bfsQ[tail++] = center;
    while (head < tail) {
        int idx = bfsQ[head++];
        int r = idx / 11, c = idx % 11;
        int8_t nd = dist[idx] + 1;
        if (canUpB(b, r, c) && dist[idx - 11] == -1) { dist[idx - 11] = nd; bfsQ[tail++] = idx - 11; }
        if (canDownB(b, r, c) && dist[idx + 11] == -1) { dist[idx + 11] = nd; bfsQ[tail++] = idx + 11; }
        if (canLeftB(b, r, c) && dist[idx - 1] == -1) { dist[idx - 1] = nd; bfsQ[tail++] = idx - 1; }
        if (canRightB(b, r, c) && dist[idx + 1] == -1) { dist[idx + 1] = nd; bfsQ[tail++] = idx + 1; }
    }

    int mr = quadP[0].r, mc = quadP[0].c;
    int bestD = 999, bestR = mr, bestC = mc;
    for (int d = 0; d < 4; d++) {
        if (!canStepDirB(b, mr, mc, d)) continue;
        int nr = mr + DR[d], nc = mc + DC[d];
        if (nr == 5 && nc == 5) return packMove16(STEP, 5, 5, 0);
        int cd = dist[nr * 11 + nc];
        if (cd >= 0 && cd < bestD) { bestD = cd; bestR = nr; bestC = nc; }
    }
    return packMove16(STEP, bestR, bestC, 0);
}

extern "C" {

EXPORT_FN void initEngine() {
    rngState = 0x13579BDFU;
}

EXPORT_FN int getNodesSearched() {
    return (int)totalSimulationsRun;
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

    BoardState root;
    memset(&root, 0, sizeof(root));
    root.pR[0] = mR; root.pC[0] = mC; root.pWalls[0] = mW;
    root.pR[1] = oR; root.pC[1] = oC; root.pWalls[1] = oW;
    root.turn = 0;
    root.totalWalls = 0;

    if (wallListStr && strlen(wallListStr) > 0) {
        char buf[4096];
        strncpy(buf, wallListStr, sizeof(buf) - 1);
        buf[sizeof(buf) - 1] = '\0';
        char* token = strtok(buf, ";");
        while (token) {
            int wr, wc; char wo;
            if (sscanf(token, "%d,%d,%c", &wr, &wc, &wo) == 3) {
                int idx = wr * (B_COLS - 1) + wc;
                if (wo == 'h') root.hWalls[idx] = 1; else root.vWalls[idx] = 1;
                root.totalWalls++;
            }
            token = strtok(nullptr, ";");
        }
    }

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
        return searchQuadSimple(root);
    }

    int budget = max(500, min(5000, timeMs));
    return (int)runNemesisMCTS(root, budget, 60000);
}

} // extern "C"
