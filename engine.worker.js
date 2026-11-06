javascript
"use strict";

// ============================================================================
// WALLHACK PRO WORKER:
// 1. Uses compiled C++ WebAssembly (engine.wasm + engine.js) when present.
// 2. Includes the complete Zobrist PVS/LMR engine in JS so it works at 100%
//    strength immediately even before GitHub Actions finishes compiling WASM.
// ============================================================================

let wasmApi = null;
let wasmReady = false;

function tryInitWasm() {
  try {
    importScripts("engine.js");
    if (typeof Module !== "undefined") {
      const bindApi = () => {
        try {
          wasmApi = {
            init: Module.cwrap("initEngine", null, []),
            search: Module.cwrap("search", "number", [
              "number", "number", "number",
              "number", "number", "number",
              "number", "number", "number",
              "string", "string", "number", "number"
            ]),
            getNodes: Module.cwrap("getNodesSearched", "number", []),
            getDepth: Module.cwrap("getCompletedDepth", "number", [])
          };
          wasmApi.init();
          wasmReady = true;
        } catch (e) {
          wasmReady = false;
        }
      };
      if (Module.calledRun) {
        bindApi();
      } else {
        Module.onRuntimeInitialized = bindApi;
      }
    }
  } catch (e) {
    wasmReady = false;
  }
}

tryInitWasm();

// ============================================================================
// HIGH-SPEED BIT-ARRAY JS PVS ENGINE (SYNCHRONIZED WITH C++ ARCHITECTURE)
// ============================================================================
let boardRows = 9;
let boardCols = 9;
let isRaceMode = false;
let isQuadMode = false;
let deadline = 0;
let timedOut = false;
let nodes = 0;
let ttHits = 0;
let cutoffs = 0;
let completedDepth = 0;

const hWalls = new Uint8Array(169);
const vWalls = new Uint8Array(169);
let myR = 8, myC = 4, oppR = 0, oppC = 4;
let myWalls = 10, oppWalls = 10;
let totalWallsPlaced = 0;
let wHashLo = 0, wHashHi = 0;

const Z_HWALL_LO = new Uint32Array(169);
const Z_HWALL_HI = new Uint32Array(169);
const Z_VWALL_LO = new Uint32Array(169);
const Z_VWALL_HI = new Uint32Array(169);
const Z_ME_LO = new Uint32Array(169);
const Z_ME_HI = new Uint32Array(169);
const Z_OPP_LO = new Uint32Array(169);
const Z_OPP_HI = new Uint32Array(169);
const Z_MW_LO = new Uint32Array(20);
const Z_MW_HI = new Uint32Array(20);
const Z_OW_LO = new Uint32Array(20);
const Z_OW_HI = new Uint32Array(20);

(function initZobristJS() {
  let seed = 0x9e3779b9;
  function rand32() {
    seed |= 0;
    seed = (seed + 0x6d2b79f5) | 0;
    let t = Math.imul(seed ^ (seed >>> 15), 1 | seed);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return (t ^ (t >>> 14)) >>> 0;
  }
  for (let i = 0; i < 169; i++) {
    Z_HWALL_LO[i] = rand32(); Z_HWALL_HI[i] = rand32();
    Z_VWALL_LO[i] = rand32(); Z_VWALL_HI[i] = rand32();
    Z_ME_LO[i] = rand32();    Z_ME_HI[i] = rand32();
    Z_OPP_LO[i] = rand32();   Z_OPP_HI[i] = rand32();
  }
  for (let i = 0; i < 20; i++) {
    Z_MW_LO[i] = rand32(); Z_MW_HI[i] = rand32();
    Z_OW_LO[i] = rand32(); Z_OW_HI[i] = rand32();
  }
})();

// Нелинейная стоимость запаса стен (как в C++ ядре)
const WALL_VAL_TABLE = [
  0, 550, 980, 1340, 1650, 1920, 2160, 2380, 2580, 2760, 2930, 3090, 3240, 3380, 3510, 3630
];

const TT = new Map();
const wallDistCache = new Map();
const killer = Array.from({ length: 64 }, () => [0, 0]);
const history = new Int32Array(2048);
const bfsQ = new Int16Array(256);

function now() {
  return typeof performance !== "undefined" ? performance.now() : Date.now();
}

function canUp(r, c) {
  if (r <= 0) return false;
  const maxW = boardCols - 1;
  const base = (r - 1) * maxW;
  return (c >= maxW || hWalls[base + c] === 0) && (c <= 0 || hWalls[base + c - 1] === 0);
}
function canDown(r, c) {
  if (r >= boardRows - 1) return false;
  const maxW = boardCols - 1;
  const base = r * maxW;
  return (c >= maxW || hWalls[base + c] === 0) && (c <= 0 || hWalls[base + c - 1] === 0);
}
function canLeft(r, c) {
  if (c <= 0) return false;
  const maxW = boardCols - 1;
  const col = c - 1;
  return (r >= boardRows - 1 || vWalls[r * maxW + col] === 0) && (r <= 0 || vWalls[(r - 1) * maxW + col] === 0);
}
function canRight(r, c) {
  const maxW = boardCols - 1;
  if (c >= maxW) return false;
  return (r >= boardRows - 1 || vWalls[r * maxW + c] === 0) && (r <= 0 || vWalls[(r - 1) * maxW + c] === 0);
}

function canStepDir(r, c, dir) {
  if (dir === 0) return canUp(r, c);
  if (dir === 1) return canDown(r, c);
  if (dir === 2) return canLeft(r, c);
  return canRight(r, c);
}

function wallGeometryLegal(r, c, o) {
  const maxR = boardRows - 2;
  const maxC = boardCols - 2;
  if (r < 0 || r > maxR || c < 0 || c > maxC) return false;
  const stride = boardCols - 1;
  const idx = r * stride + c;
  if (o === 0) {
    if (hWalls[idx] || vWalls[idx]) return false;
    if ((c > 0 && hWalls[idx - 1]) || (c < maxC && hWalls[idx + 1])) return false;
    return true;
  } else {
    if (vWalls[idx] || hWalls[idx]) return false;
    if ((r > 0 && vWalls[idx - stride]) || (r < maxR && vWalls[idx + stride])) return false;
    return true;
  }
}

function placeWallFast(r, c, o) {
  const idx = r * (boardCols - 1) + c;
  if (o === 0) {
    hWalls[idx] = 1;
    wHashLo = (wHashLo ^ Z_HWALL_LO[idx]) >>> 0;
    wHashHi = (wHashHi ^ Z_HWALL_HI[idx]) >>> 0;
  } else {
    vWalls[idx] = 1;
    wHashLo = (wHashLo ^ Z_VWALL_LO[idx]) >>> 0;
    wHashHi = (wHashHi ^ Z_VWALL_HI[idx]) >>> 0;
  }
  totalWallsPlaced++;
}

function removeWallFast(r, c, o) {
  const idx = r * (boardCols - 1) + c;
  if (o === 0) {
    hWalls[idx] = 0;
    wHashLo = (wHashLo ^ Z_HWALL_LO[idx]) >>> 0;
    wHashHi = (wHashHi ^ Z_HWALL_HI[idx]) >>> 0;
  } else {
    vWalls[idx] = 0;
    wHashLo = (wHashLo ^ Z_VWALL_LO[idx]) >>> 0;
    wHashHi = (wHashHi ^ Z_VWALL_HI[idx]) >>> 0;
  }
  totalWallsPlaced--;
}

function computeGoalMap(goalRow) {
  const total = boardRows * 9;
  const dist = new Int8Array(total);
  dist.fill(-1);
  let head = 0, tail = 0;
  const baseGoal = goalRow * 9;
  for (let c = 0; c < 9; c++) {
    const idx = baseGoal + c;
    dist[idx] = 0;
    bfsQ[tail++] = idx;
  }
  while (head < tail) {
    const idx = bfsQ[head++];
    const r = (idx / 9) | 0;
    const c = idx - r * 9;
    const nd = dist[idx] + 1;

    if (canUp(r, c)) {
      const ni = idx - 9;
      if (dist[ni] === -1) { dist[ni] = nd; bfsQ[tail++] = ni; }
    }
    if (canDown(r, c)) {
      const ni = idx + 9;
      if (dist[ni] === -1) { dist[ni] = nd; bfsQ[tail++] = ni; }
    }
    if (canLeft(r, c)) {
      const ni = idx - 1;
      if (dist[ni] === -1) { dist[ni] = nd; bfsQ[tail++] = ni; }
    }
    if (canRight(r, c)) {
      const ni = idx + 1;
      if (dist[ni] === -1) { dist[ni] = nd; bfsQ[tail++] = ni; }
    }
  }
  return dist;
}

function getDistMaps() {
  const key = wHashLo + ":" + wHashHi;
  let entry = wallDistCache.get(key);
  if (entry !== undefined) return entry;

  const meMap = computeGoalMap(0);
  const oppMap = isRaceMode ? meMap : computeGoalMap(boardRows - 1);

  entry = { meMap, oppMap };
  if (wallDistCache.size > 60000) wallDistCache.clear();
  wallDistCache.set(key, entry);
  return entry;
}

function countOptimalExits(r, c, distMap) {
  const idx = r * 9 + c;
  const d = distMap[idx];
  if (d <= 0) return 0;
  const target = d - 1;
  let exits = 0;
  if (canUp(r, c) && distMap[idx - 9] === target) exits++;
  if (canDown(r, c) && distMap[idx + 9] === target) exits++;
  if (canLeft(r, c) && distMap[idx - 1] === target) exits++;
  if (canRight(r, c) && distMap[idx + 1] === target) exits++;
  return exits;
}

const DR = [-1, 1, 0, 0];
const DC = [0, 0, -1, 1];

function getPawnSteps(pR, pC, oR, oC) {
  const out = [];
  for (let d = 0; d < 4; d++) {
    if (!canStepDir(pR, pC, d)) continue;
    const nr = pR + DR[d], nc = pC + DC[d];
    if (nr === oR && nc === oC) {
      if (canStepDir(oR, oC, d)) {
        out.push((oR + DR[d]) * 9 + (oC + DC[d]));
      } else {
        if (d < 2) {
          if (canLeft(oR, oC)) out.push(oR * 9 + (oC - 1));
          if (canRight(oR, oC)) out.push(oR * 9 + (oC + 1));
        } else {
          if (canUp(oR, oC)) out.push((oR - 1) * 9 + oC);
          if (canDown(oR, oC)) out.push((oR + 1) * 9 + oC);
        }
      }
    } else {
      out.push(nr * 9 + nc);
    }
  }
  return out;
}

function evaluatePosition(isMyTurn) {
  const oppGoal = isRaceMode ? 0 : boardRows - 1;
  if (myR === 0) return 100000000;
  if (oppR === oppGoal) return -100000000;

  const maps = getDistMaps();
  const myIdx = myR * 9 + myC;
  const oppIdx = oppR * 9 + oppC;
  const myDist = maps.meMap[myIdx];
  const oppDist = maps.oppMap[oppIdx];

  if (myDist < 0) return -100000000;
  if (oppDist < 0) return 100000000;

  const tempo = isMyTurn ? 750 : -750;
  const myExits = countOptimalExits(myR, myC, maps.meMap);
  const oppExits = countOptimalExits(oppR, oppC, maps.oppMap);

  const mwVal = WALL_VAL_TABLE[Math.min(15, Math.max(0, myWalls))];
  const owVal = WALL_VAL_TABLE[Math.min(15, Math.max(0, oppWalls))];

  let score = (oppDist - myDist) * 1600 + tempo + (mwVal - owVal);
  if (myWalls === 0 && oppWalls > 0) score -= 1200;
  if (oppWalls === 0 && myWalls > 0) score += 1200;

  score += (myExits - oppExits) * 145;
  if (oppExits <= 1 && myWalls > 0) score += 320;
  if (myExits <= 1 && oppWalls > 0) score -= 340;

  if (isRaceMode) {
    if (myDist <= oppDist) score += Math.abs(myC - oppC) * 22;
    if (myDist <= 4 || oppDist <= 4) score += (oppDist - myDist) * 520;
  } else {
    if (Math.abs(myR - oppR) + Math.abs(myC - oppC) === 1) {
      if (isMyTurn) {
        const steps = getPawnSteps(myR, myC, oppR, oppC);
        for (let i = 0; i < steps.length; i++) {
          if (maps.meMap[steps[i]] <= myDist - 2) { score += 1050; break; }
        }
      } else {
        const steps = getPawnSteps(oppR, oppC, myR, myC);
        for (let i = 0; i < steps.length; i++) {
          if (maps.oppMap[steps[i]] <= oppDist - 2) { score -= 1050; break; }
        }
      }
    }
    const myCenter = 4 - Math.abs(myC - 4);
    const oppCenter = 4 - Math.abs(oppC - 4);
    score += (myCenter - oppCenter) * 16;
    if (myDist <= 3 || oppDist <= 3) score += (oppDist - myDist) * 520;
  }
  return score;
}

function packMove(type, r, c, o) {
  return (type & 1) | ((o & 1) << 1) | ((r & 15) << 2) | ((c & 15) << 6);
}
function unpackMove(code) {
  return {
    type: code & 1,
    o: (code >>> 1) & 1,
    r: (code >>> 2) & 15,
    c: (code >>> 6) & 15
  };
}

function sortMoves(codes, prios) {
  const n = codes.length;
  for (let i = 1; i < n; i++) {
    const c = codes[i], p = prios[i];
    let j = i - 1;
    while (j >= 0 && prios[j] < p) {
      codes[j + 1] = codes[j];
      prios[j + 1] = prios[j];
      j--;
    }
    codes[j + 1] = c;
    prios[j + 1] = p;
  }
  return codes;
}

function generateMoves(maximizing, depth, ttBestCode, isRoot) {
  const pR = maximizing ? myR : oppR;
  const pC = maximizing ? myC : oppC;
  const eR = maximizing ? oppR : myR;
  const eC = maximizing ? oppC : myC;
  const pWalls = maximizing ? myWalls : oppWalls;
  const pGoal = maximizing ? 0 : (isRaceMode ? 0 : boardRows - 1);

  const maps = getDistMaps();
  const pMap = maximizing ? maps.meMap : maps.oppMap;
  const eMap = maximizing ? maps.oppMap : maps.meMap;

  const curP = pMap[pR * 9 + pC];
  const curE = eMap[eR * 9 + eC];
  const curEExits = countOptimalExits(eR, eC, eMap);

  const moveCodes = [];
  const movePrios = [];

  const steps = getPawnSteps(pR, pC, eR, eC);
  for (let i = 0; i < steps.length; i++) {
    const cell = steps[i];
    const sr = (cell / 9) | 0;
    const sc = cell - sr * 9;
    const code = packMove(0, sr, sc, 0);
    if (sr === pGoal) return [code];

    const newD = pMap[cell];
    const stepGain = curP - newD;
    let prio = stepGain * 12000 + history[code];
    if (code === ttBestCode) prio += 5000000;
    if (stepGain >= 2) prio += 9000;

    moveCodes.push(code);
    movePrios.push(prio);
  }

  if (pWalls <= 0) return sortMoves(moveCodes, movePrios);

  const maxR = boardRows - 2;
  const wallCodes = [];
  const wallPrios = [];

  for (let r = 0; r <= maxR; r++) {
    for (let c = 0; c < 8; c++) {
      const idxTL = r * 9 + c;
      const dTL = eMap[idxTL];
      const dTR = eMap[idxTL + 1];
      const dBL = eMap[idxTL + 9];
      const dBR = eMap[idxTL + 10];

      const nearEnemy = Math.abs(r - eR) <= 3 && Math.abs(c - eC) <= 3;
      const nearMe = Math.abs(r - pR) <= 2 && Math.abs(c - pC) <= 2;

      for (let o = 0; o < 2; o++) {
        if (!wallGeometryLegal(r, c, o)) continue;

        let cutsGradient = false;
        if (o === 0) {
          cutsGradient = (Math.abs(dTL - dBL) === 1 && Math.min(dTL, dBL) < curE) ||
                         (Math.abs(dTR - dBR) === 1 && Math.min(dTR, dBR) < curE);
        } else {
          cutsGradient = (Math.abs(dTL - dTR) === 1 && Math.min(dTL, dTR) < curE) ||
                         (Math.abs(dBL - dBR) === 1 && Math.min(dBL, dBR) < curE);
        }

        if (!isRoot && !cutsGradient && !nearEnemy && !nearMe) continue;

        placeWallFast(r, c, o);
        const newMaps = getDistMaps();
        const nPMap = maximizing ? newMaps.meMap : newMaps.oppMap;
        const nEMap = maximizing ? newMaps.oppMap : newMaps.meMap;
        const newP = nPMap[pR * 9 + pC];
        const newE = nEMap[eR * 9 + eC];
        removeWallFast(r, c, o);

        if (newP < 0 || newE < 0) continue;

        const eGain = newE - curE;
        const pLoss = newP - curP;
        const netDelta = eGain - pLoss;

        const newEExits = countOptimalExits(eR, eC, nEMap);
        const exitDrop = curEExits - newEExits;

        if (!isRoot && netDelta < 0 && exitDrop <= 0) continue;
        if (!isRoot && netDelta === 0 && exitDrop <= 0 && !nearEnemy) continue;

        const code = packMove(1, r, c, o);
        let prio = netDelta * 7500 + eGain * 2600 + exitDrop * 2000 + history[code];

        if (code === ttBestCode) prio += 5000000;
        if (killer[depth][0] === code || killer[depth][1] === code) prio += 6000;

        if (isRaceMode) {
          if (o === 1 && Math.abs(c - eC) <= 1 && Math.abs(r - eR) <= 2) prio += 1200;
          if (pLoss > 0) prio -= pLoss * 2800;
        } else {
          if (eGain >= 2 && pLoss === 0) prio += 4500;
        }

        wallCodes.push(code);
        wallPrios.push(prio);
      }
    }
  }

  const sortedWalls = sortMoves(wallCodes, wallPrios);
  const wallLimit = isRoot ? 44 : (depth >= 5 ? 12 : (depth >= 3 ? 16 : 20));
  const take = Math.min(wallLimit, sortedWalls.length);

  for (let i = 0; i < take; i++) {
    const wCode = sortedWalls[i];
    const idx = wallCodes.indexOf(wCode);
    moveCodes.push(wCode);
    movePrios.push(wallPrios[idx]);
  }
  return sortMoves(moveCodes, movePrios);
}

function getFullStateKey(maximizing) {
  const meIdx = myR * 9 + myC;
  const oppIdx = oppR * 9 + oppC;
  const lo = (wHashLo ^ Z_ME_LO[meIdx] ^ Z_OPP_LO[oppIdx] ^ Z_MW_LO[myWalls] ^ Z_OW_LO[oppWalls]) >>> 0;
  const hi = (wHashHi ^ Z_ME_HI[meIdx] ^ Z_OPP_HI[oppIdx] ^ Z_MW_HI[myWalls] ^ Z_OW_HI[oppWalls] ^ (maximizing ? 0x12345678 : 0)) >>> 0;
  return lo + ":" + hi;
}

function pvs(depth, maximizing, alpha, beta) {
  if ((++nodes & 127) === 0 && now() >= deadline) {
    timedOut = true;
    return 0;
  }

  const oppGoal = isRaceMode ? 0 : boardRows - 1;
  if (myR === 0) return 100000000 + depth;
  if (oppR === oppGoal) return -100000000 - depth;
  if (depth <= 0) return evaluatePosition(maximizing);

  const ttKey = getFullStateKey(maximizing);
  const hit = TT.get(ttKey);
  let ttBestCode = -1;

  if (hit !== undefined) {
    ttBestCode = hit.bestMove;
    if (hit.depth >= depth) {
      ttHits++;
      if (hit.flag === 0) return hit.score;
      if (hit.flag === 1 && hit.score > alpha) alpha = hit.score;
      else if (hit.flag === 2 && hit.score < beta) beta = hit.score;
      if (alpha >= beta) { cutoffs++; return hit.score; }
    }
  }

  const alpha0 = alpha;
  const moves = generateMoves(maximizing, depth, ttBestCode, false);
  if (moves.length === 0) return evaluatePosition(maximizing);

  let bestScore = maximizing ? -Infinity : Infinity;
  let bestMoveCode = moves[0];

  for (let i = 0; i < moves.length; i++) {
    const code = moves[i];
    const mType = code & 1;
    const mO = (code >>> 1) & 1;
    const mR = (code >>> 2) & 15;
    const mC = (code >>> 6) & 15;

    let savedR = 0, savedC = 0;
    if (mType === 0) {
      if (maximizing) { savedR = myR; savedC = myC; myR = mR; myC = mC; }
      else { savedR = oppR; savedC = oppC; oppR = mR; oppC = mC; }
    } else {
      placeWallFast(mR, mC, mO);
      if (maximizing) myWalls--; else oppWalls--;
    }

    let nextDepth = depth - 1;
    if (depth >= 4 && i >= 7 && mType === 1) nextDepth = depth - 2;

    let val = pvs(nextDepth, !maximizing, alpha, beta);

    if (!timedOut && nextDepth < depth - 1) {
      if ((maximizing && val > alpha) || (!maximizing && val < beta)) {
        val = pvs(depth - 1, !maximizing, alpha, beta);
      }
    }

    if (mType === 0) {
      if (maximizing) { myR = savedR; myC = savedC; }
      else { oppR = savedR; oppC = savedC; }
    } else {
      removeWallFast(mR, mC, mO);
      if (maximizing) myWalls++; else oppWalls++;
    }

    if (timedOut) return 0;

    if (maximizing) {
      if (val > bestScore) { bestScore = val; bestMoveCode = code; }
      if (bestScore > alpha) alpha = bestScore;
    } else {
      if (val < bestScore) { bestScore = val; bestMoveCode = code; }
      if (bestScore < beta) beta = bestScore;
    }

    if (beta <= alpha) {
      cutoffs++;
      if (killer[depth][0] !== code) {
        killer[depth][1] = killer[depth][0];
        killer[depth][0] = code;
      }
      history[code] = Math.min(300000, history[code] + depth * depth * 70);
      break;
    }
  }

  let flag = 0;
  if (bestScore <= alpha0) flag = 2;
  else if (bestScore >= beta) flag = 1;

  if (TT.size > 150000) TT.clear();
  TT.set(ttKey, { depth, score: bestScore, flag, bestMove: bestMoveCode });
  return bestScore;
}

function searchBestMoveJS(timeBudgetMs, maxSearchDepth) {
  TT.clear();
  history.fill(0);
  for (let i = 0; i < 64; i++) { killer[i][0] = 0; killer[i][1] = 0; }

  nodes = 0; ttHits = 0; cutoffs = 0; timedOut = false; completedDepth = 0;
  deadline = now() + timeBudgetMs;

  const rootMoves = generateMoves(true, 1, -1, true);
  if (rootMoves.length === 0) return null;

  const firstUnpacked = unpackMove(rootMoves[0]);
  if (firstUnpacked.type === 0 && firstUnpacked.r === 0) {
    completedDepth = 1;
    return firstUnpacked;
  }

  let bestCode = rootMoves[0];

  for (let depth = 1; depth <= maxSearchDepth; depth++) {
    if (now() >= deadline) break;
    timedOut = false;

    let iterBestCode = bestCode;
    let iterBestScore = -Infinity;
    let alpha = -Infinity;

    const ordered = [bestCode];
    for (let i = 0; i < rootMoves.length; i++) {
      if (rootMoves[i] !== bestCode) ordered.push(rootMoves[i]);
    }

    for (let i = 0; i < ordered.length; i++) {
      const code = ordered[i];
      const mType = code & 1;
      const mO = (code >>> 1) & 1;
      const mR = (code >>> 2) & 15;
      const mC = (code >>> 6) & 15;

      let savedR = myR, savedC = myC;
      if (mType === 0) {
        myR = mR; myC = mC;
      } else {
        placeWallFast(mR, mC, mO);
        myWalls--;
      }

      const score = pvs(depth - 1, false, alpha, Infinity);

      if (mType === 0) {
        myR = savedR; myC = savedC;
      } else {
        removeWallFast(mR, mC, mO);
        myWalls++;
      }

      if (timedOut) break;
      if (score > iterBestScore) {
        iterBestScore = score;
        iterBestCode = code;
      }
      if (score > alpha) alpha = score;
    }

    if (!timedOut) {
      bestCode = iterBestCode;
      completedDepth = depth;
      if (iterBestScore >= 90000000) break;
    } else {
      break;
    }
  }
  return unpackMove(bestCode);
}

// Quad 11x11 JS Engine
let quadPlayers = [];

function computeCenterMap11() {
  const key = "Q:" + wHashLo + ":" + wHashHi;
  let dist = wallDistCache.get(key);
  if (dist !== undefined) return dist;

  dist = new Int8Array(121);
  dist.fill(-1);
  let head = 0, tail = 0;
  const centerIdx = 5 * 11 + 5;
  dist[centerIdx] = 0;
  bfsQ[tail++] = centerIdx;

  while (head < tail) {
    const idx = bfsQ[head++];
    const r = (idx / 11) | 0;
    const c = idx - r * 11;
    const nd = dist[idx] + 1;

    if (canUp(r, c)) {
      const ni = idx - 11;
      if (dist[ni] === -1) { dist[ni] = nd; bfsQ[tail++] = ni; }
    }
    if (canDown(r, c)) {
      const ni = idx + 11;
      if (dist[ni] === -1) { dist[ni] = nd; bfsQ[tail++] = ni; }
    }
    if (canLeft(r, c)) {
      const ni = idx - 1;
      if (dist[ni] === -1) { dist[ni] = nd; bfsQ[tail++] = ni; }
    }
    if (canRight(r, c)) {
      const ni = idx + 1;
      if (dist[ni] === -1) { dist[ni] = nd; bfsQ[tail++] = ni; }
    }
  }
  if (wallDistCache.size > 50000) wallDistCache.clear();
  wallDistCache.set(key, dist);
  return dist;
}

function countExits11(r, c, dist) {
  const idx = r * 11 + c;
  const d = dist[idx];
  if (d <= 0) return 0;
  const target = d - 1;
  let ex = 0;
  if (canUp(r, c) && dist[idx - 11] === target) ex++;
  if (canDown(r, c) && dist[idx + 11] === target) ex++;
  if (canLeft(r, c) && dist[idx - 1] === target) ex++;
  if (canRight(r, c) && dist[idx + 1] === target) ex++;
  return ex;
}

function isCellOccupiedQuad(r, c, ignoreIdx) {
  for (let i = 0; i < quadPlayers.length; i++) {
    if (i !== ignoreIdx && quadPlayers[i].active && quadPlayers[i].r === r && quadPlayers[i].c === c) return true;
  }
  return false;
}

function getQuadSteps(pIdx) {
  const p = quadPlayers[pIdx];
  const out = [];
  for (let d = 0; d < 4; d++) {
    if (!canStepDir(p.r, p.c, d)) continue;
    const nr = p.r + DR[d], nc = p.c + DC[d];
    if (isCellOccupiedQuad(nr, nc, pIdx)) {
      const jr = nr + DR[d], jc = nc + DC[d];
      if (jr >= 0 && jr < 11 && jc >= 0 && jc < 11 && canStepDir(nr, nc, d) && !isCellOccupiedQuad(jr, jc, pIdx)) {
        out.push({ r: jr, c: jc });
      } else {
        if (d < 2) {
          if (canLeft(nr, nc) && !isCellOccupiedQuad(nr, nc - 1, pIdx)) out.push({ r: nr, c: nc - 1 });
          if (canRight(nr, nc) && !isCellOccupiedQuad(nr, nc + 1, pIdx)) out.push({ r: nr, c: nc + 1 });
        } else {
          if (canUp(nr, nc) && !isCellOccupiedQuad(nr - 1, nc, pIdx)) out.push({ r: nr - 1, c: nc });
          if (canDown(nr, nc) && !isCellOccupiedQuad(nr + 1, nc, pIdx)) out.push({ r: nr + 1, c: nc });
        }
      }
    } else {
      out.push({ r: nr, c: nc });
    }
  }
  return out;
}

function evaluateQuadState(myTurnNow) {
  const me = quadPlayers[0];
  if (me.r === 5 && me.c === 5) return 100000000;

  const dist = computeCenterMap11();
  const myD = dist[me.r * 11 + me.c];
  if (myD < 0) return -100000000;

  let minOppEffDist = 999;
  let secondOppEffDist = 999;
  let leaderIdx = 1;

  for (let i = 1; i < quadPlayers.length; i++) {
    const op = quadPlayers[i];
    if (!op.active) continue;
    if (op.r === 5 && op.c === 5) return -100000000;
    const od = dist[op.r * 11 + op.c];
    if (od < 0) return 100000000;

    const turnAdvantage = myTurnNow ? (0.15 * i) : (-0.65 + 0.15 * i);
    const eff = od + turnAdvantage;
    if (eff < minOppEffDist) {
      secondOppEffDist = minOppEffDist;
      minOppEffDist = eff;
      leaderIdx = i;
    } else if (eff < secondOppEffDist) {
      secondOppEffDist = eff;
    }
  }

  const myExits = countExits11(me.r, me.c, dist);
  const leader = quadPlayers[leaderIdx];
  const leaderExits = leader && leader.active ? countExits11(leader.r, leader.c, dist) : 2;

  let score = (minOppEffDist - myD) * 2000;
  if (secondOppEffDist < 900) score += (secondOppEffDist - myD) * 450;
  score += me.walls * 185;
  if (me.walls === 0 && minOppEffDist <= myD) score -= 2200;
  score += (myExits - leaderExits) * 190;
  if (canDown(5, 5) && me.r > 5) score += 320;
  return score;
}

function generateQuadMoves(pIdx, isRoot) {
  const p = quadPlayers[pIdx];
  const dist = computeCenterMap11();
  const curD = dist[p.r * 11 + p.c];
  const moves = [];

  const steps = getQuadSteps(pIdx);
  for (let i = 0; i < steps.length; i++) {
    const st = steps[i];
    if (st.r === 5 && st.c === 5) return [{ type: 0, r: st.r, c: st.c, o: 0, prio: 1e12 }];
    const nd = dist[st.r * 11 + st.c];
    const gain = curD - nd;
    let prio = gain * 9500;
    if (gain >= 2) prio += 5000;
    moves.push({ type: 0, r: st.r, c: st.c, o: 0, prio });
  }

  if (p.walls <= 0) return moves.sort((a, b) => b.prio - a.prio);

  let targetIdx = 0;
  let bestTargetDist = 999;
  for (let i = 0; i < quadPlayers.length; i++) {
    if (i === pIdx || !quadPlayers[i].active) continue;
    const d = dist[quadPlayers[i].r * 11 + quadPlayers[i].c];
    if (d < bestTargetDist) {
      bestTargetDist = d;
      targetIdx = i;
    }
  }

  if (!isRoot && pIdx === 0 && curD + 1 < bestTargetDist) {
    return moves.sort((a, b) => b.prio - a.prio);
  }

  const target = quadPlayers[targetIdx];
  const wallCands = [];

  for (let r = 0; r <= 9; r++) {
    for (let c = 0; c <= 9; c++) {
      const nearCenter = Math.abs(r - 4.5) <= 2 && Math.abs(c - 4.5) <= 2;
      const nearTarget = Math.abs(r - target.r) <= 2 && Math.abs(c - target.c) <= 2;
      if (!nearCenter && !nearTarget) continue;

      for (let o = 0; o < 2; o++) {
        if (!wallGeometryLegal(r, c, o)) continue;

        placeWallFast(r, c, o);
        const newDist = computeCenterMap11();
        let legal = true;
        for (let i = 0; i < quadPlayers.length; i++) {
          if (quadPlayers[i].active && newDist[quadPlayers[i].r * 11 + quadPlayers[i].c] < 0) {
            legal = false;
            break;
          }
        }
        const newMyD = newDist[p.r * 11 + p.c];
        const newTargetD = newDist[target.r * 11 + target.c];
        removeWallFast(r, c, o);

        if (!legal) continue;

        const targetDelay = newTargetD - bestTargetDist;
        const selfLoss = newMyD - curD;
        const net = targetDelay - selfLoss;

        if (net <= 0) continue;

        let prio = net * 6800 + targetDelay * 2400;
        if (nearCenter && targetDelay >= 1 && selfLoss === 0) prio += 3400;
        wallCands.push({ type: 1, r, c, o, prio });
      }
    }
  }

  wallCands.sort((a, b) => b.prio - a.prio);
  const limit = isRoot ? 24 : 10;
  for (let i = 0; i < Math.min(limit, wallCands.length); i++) {
    moves.push(wallCands[i]);
  }
  return moves.sort((a, b) => b.prio - a.prio);
}

function simulateOpponentsRound(depth, alpha, beta) {
  const dist = computeCenterMap11();
  let leaderIdx = -1;
  let minD = 999;
  for (let i = 1; i < quadPlayers.length; i++) {
    if (!quadPlayers[i].active) continue;
    const d = dist[quadPlayers[i].r * 11 + quadPlayers[i].c];
    if (d < minD) { minD = d; leaderIdx = i; }
  }
  if (leaderIdx === -1) return evaluateQuadState(true);

  const savedPos = [];
  for (let i = 1; i < quadPlayers.length; i++) {
    const op = quadPlayers[i];
    savedPos.push({ r: op.r, c: op.c });
    if (!op.active || i === leaderIdx) continue;
    const st = getQuadSteps(i);
    let bestR = op.r, bestC = op.c, bestD = dist[op.r * 11 + op.c];
    for (let k = 0; k < st.length; k++) {
      const nd = dist[st[k].r * 11 + st[k].c];
      if (nd >= 0 && nd < bestD) { bestD = nd; bestR = st[k].r; bestC = st[k].c; }
    }
    op.r = bestR; op.c = bestC;
  }

  const leaderMoves = generateQuadMoves(leaderIdx, false);
  const leader = quadPlayers[leaderIdx];
  let worstForMe = Infinity;

  for (let i = 0; i < Math.min(leaderMoves.length, 10); i++) {
    const m = leaderMoves[i];
    const sr = leader.r, sc = leader.c;
    if (m.type === 0) {
      leader.r = m.r; leader.c = m.c;
    } else {
      placeWallFast(m.r, m.c, m.o);
      leader.walls--;
    }

    const val = quadSearchMe(depth - 1, alpha, worstForMe);

    if (m.type === 0) {
      leader.r = sr; leader.c = sc;
    } else {
      removeWallFast(m.r, m.c, m.o);
      leader.walls++;
    }

    if (timedOut) break;
    if (val < worstForMe) worstForMe = val;
    if (worstForMe <= alpha) { cutoffs++; break; }
  }

  for (let i = 1; i < quadPlayers.length; i++) {
    quadPlayers[i].r = savedPos[i - 1].r;
    quadPlayers[i].c = savedPos[i - 1].c;
  }
  return worstForMe;
}

function quadSearchMe(depth, alpha, beta) {
  if ((++nodes & 63) === 0 && now() >= deadline) {
    timedOut = true;
    return 0;
  }
  if (quadPlayers[0].r === 5 && quadPlayers[0].c === 5) return 100000000 + depth;
  for (let i = 1; i < quadPlayers.length; i++) {
    if (quadPlayers[i].active && quadPlayers[i].r === 5 && quadPlayers[i].c === 5) return -100000000 - depth;
  }
  if (depth <= 0) return evaluateQuadState(true);

  const myMoves = generateQuadMoves(0, false);
  if (!myMoves.length) return evaluateQuadState(true);

  let best = -Infinity;
  const me = quadPlayers[0];

  for (let i = 0; i < Math.min(myMoves.length, 14); i++) {
    const m = myMoves[i];
    const sr = me.r, sc = me.c;
    if (m.type === 0) {
      me.r = m.r; me.c = m.c;
    } else {
      placeWallFast(m.r, m.c, m.o);
      me.walls--;
    }

    const val = (me.r === 5 && me.c === 5)
      ? (100000000 + depth)
      : simulateOpponentsRound(depth - 1, Math.max(alpha, best), beta);

    if (m.type === 0) {
      me.r = sr; me.c = sc;
    } else {
      removeWallFast(m.r, m.c, m.o);
      me.walls++;
    }

    if (timedOut) return 0;
    if (val > best) best = val;
    if (best >= beta) { cutoffs++; break; }
  }
  return best;
}

function searchBestQuadMoveJS(timeBudgetMs) {
  nodes = 0; ttHits = 0; cutoffs = 0; timedOut = false; completedDepth = 0;
  deadline = now() + timeBudgetMs;

  const rootMoves = generateQuadMoves(0, true);
  if (!rootMoves.length) return null;
  if (rootMoves[0].type === 0 && rootMoves[0].r === 5 && rootMoves[0].c === 5) {
    completedDepth = 1;
    return rootMoves[0];
  }

  let bestMove = rootMoves[0];
  const me = quadPlayers[0];

  for (let depth = 1; depth <= 6; depth++) {
    if (now() >= deadline) break;
    timedOut = false;
    let iterBest = bestMove;
    let iterScore = -Infinity;

    for (let i = 0; i < rootMoves.length; i++) {
      const m = rootMoves[i];
      const sr = me.r, sc = me.c;
      if (m.type === 0) {
        me.r = m.r; me.c = m.c;
      } else {
        placeWallFast(m.r, m.c, m.o);
        me.walls--;
      }

      const score = simulateOpponentsRound(depth - 1, iterScore, Infinity);

      if (m.type === 0) {
        me.r = sr; me.c = sc;
      } else {
        removeWallFast(m.r, m.c, m.o);
        me.walls++;
      }

      if (timedOut) break;
      if (score > iterScore) {
        iterScore = score;
        iterBest = m;
      }
    }

    if (!timedOut) {
      bestMove = iterBest;
      completedDepth = depth;
      if (iterScore >= 90000000) break;
    } else {
      break;
    }
  }
  return bestMove;
}

function loadBoardWalls(m) {
  hWalls.fill(0);
  vWalls.fill(0);
  wHashLo = 0;
  wHashHi = 0;
  totalWallsPlaced = 0;

  if (Array.isArray(m.wallList)) {
    for (let i = 0; i < m.wallList.length; i++) {
      const parts = String(m.wallList[i]).split(",");
      const r = +parts[0], c = +parts[1], o = parts[2] === "h" ? 0 : 1;
      placeWallFast(r, c, o);
    }
  }
}

self.onmessage = function (e) {
  const m = e.data || {};
  try {
    if (m.type === "init") {
      self.postMessage({ type: "ready" });
      return;
    }
    if (m.type !== "search") return;

    const newRows = Number(m.rows) || 9;
    const newCols = Number(m.cols) || 9;
    if (newRows !== boardRows || newCols !== boardCols) {
      boardRows = newRows;
      boardCols = newCols;
      wallDistCache.clear();
    }
    isQuadMode = (m.mode === "quad" || boardCols === 11);
    isRaceMode = (!isQuadMode && boardRows === 13);

    const budget = Math.max(400, Math.min(3000, Number(m.timeMs) || 1800));
    const maxD = Math.min(16, Number(m.maxDepth) || 14);
    const t0 = now();

    // 1. Если скомпилирован C++ WASM модуль — используем его
    if (wasmReady && wasmApi) {
      const modeCode = isQuadMode ? 2 : (isRaceMode ? 1 : 0);
      const wallStr = Array.isArray(m.wallList) ? m.wallList.join(";") + ";" : "";
      let quadStr = "";
      if (isQuadMode && m.players) {
        const p0 = m.players.me, p1 = m.players.left, p2 = m.players.top, p3 = m.players.right;
        quadStr = `${p0.r},${p0.c},${p0.walls},${p0.active?1:0};` +
                  `${p1.r},${p1.c},${p1.walls},${p1.active?1:0};` +
                  `${p2.r},${p2.c},${p2.walls},${p2.active?1:0};` +
                  `${p3.r},${p3.c},${p3.walls},${p3.active?1:0}`;
      }
      const packed = wasmApi.search(
        modeCode, boardRows, boardCols,
        m.my.r, m.my.c, m.my.walls,
        m.opp.r, m.opp.c, m.opp.walls,
        wallStr, quadStr, budget, maxD
      );
      const elapsed = Math.round(now() - t0);
      self.postMessage({
        type: "result",
        id: m.id,
        move: unpackMove(packed),
        nodes: wasmApi.getNodes(),
        depth: wasmApi.getDepth(),
        elapsed,
        ttHits: 0,
        cutoffs: 0
      });
      return;
    }

    // 2. Иначе выполняется синхронный высокоскоростной PVS-движок
    loadBoardWalls(m);
    let bestMove = null;
    if (isQuadMode && m.players) {
      quadPlayers = [
        { ...m.players.me },
        { ...m.players.left },
        { ...m.players.top },
        { ...m.players.right }
      ];
      bestMove = searchBestQuadMoveJS(budget);
    } else {
      myR = m.my.r; myC = m.my.c; myWalls = m.my.walls;
      oppR = m.opp.r; oppC = m.opp.c; oppWalls = m.opp.walls;
      bestMove = searchBestMoveJS(budget, maxD);
    }

    const elapsed = Math.round(now() - t0);
    self.postMessage({
      type: "result",
      id: m.id,
      move: bestMove,
      nodes,
      depth: completedDepth,
      elapsed,
      ttHits,
      cutoffs
    });
  } catch (err) {
    self.postMessage({
      type: "error",
      id: m.id,
      message: String((err && err.stack) || err)
    });
  }
};

self.postMessage({ type: "ready" });
