"use strict";

// ============================================================================
// WALLHACK GRANDMASTER ENGINE WORKER (WASM + EXACT NEMESIS/CAGE-PROBE JS CORE)
// ============================================================================

let wasmSearchFn = null;
let wasmNodesFn = null;
let wasmDepthFn = null;
let wasmReady = false;
let engineType = "js";

try {
  importScripts("engine.js");
  if (typeof createModule === "function") {
    createModule({
      locateFile: function (path) { return path; }
    }).then(function (Module) {
      const initFn = Module.cwrap("initEngine", null, []);
      initFn();
      wasmSearchFn = Module.cwrap("search", "number", [
        "number", "number", "number",
        "number", "number", "number",
        "number", "number", "number",
        "string", "string", "number", "number"
      ]);
      wasmNodesFn = Module.cwrap("getNodesSearched", "number", []);
      wasmDepthFn = Module.cwrap("getCompletedDepth", "number", []);
      wasmReady = true;
      engineType = "wasm";
      self.postMessage({ type: "ready", engine: "wasm" });
    }).catch(function () {
      engineType = "js";
      self.postMessage({ type: "ready", engine: "js" });
    });
  } else {
    self.postMessage({ type: "ready", engine: "js" });
  }
} catch (e) {
  self.postMessage({ type: "ready", engine: "js" });
}

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

const WALL_VALUE_TABLE = new Int32Array([
  0, 1450, 2700, 3800, 4800, 5720, 6580, 7390, 8150, 8860, 9500, 10100, 10680, 11240, 11780, 12300
]);

const TT_SIZE = 65536;
const TT_MASK = TT_SIZE - 1;
const ttKeyLo = new Uint32Array(TT_SIZE);
const ttKeyHi = new Uint32Array(TT_SIZE);
const ttScore = new Int32Array(TT_SIZE);
const ttDepth = new Int8Array(TT_SIZE);
const ttFlag = new Uint8Array(TT_SIZE);
const ttBestMove = new Uint16Array(TT_SIZE);

const bfsQ = new Int16Array(256);
const distMe = new Int8Array(169);
const waysMe = new Int16Array(169);
const exitsMe = new Uint8Array(169);
const distOpp = new Int8Array(169);
const waysOpp = new Int16Array(169);
const exitsOpp = new Uint8Array(169);

const killer = Array.from({ length: 64 }, () => [0, 0]);
const counterMoves = [new Uint16Array(2048), new Uint16Array(2048)];
const history = [new Int32Array(2048), new Int32Array(2048)];

const MAX_PLY = 64;
const plyMoveCodes = Array.from({ length: MAX_PLY }, () => new Int32Array(96));
const plyMovePrios = Array.from({ length: MAX_PLY }, () => new Int32Array(96));
const tempWallCodes = new Int32Array(256);
const tempWallPrios = new Int32Array(256);
const stepBuf = new Int32Array(12);

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

// Точный трафарет setWallsBesidePawn + adjustProbableValidNextWall из game.js (Nemesis)
function isNemesisProbableWall(r, c, o, pR, pC, eR, eC) {
  const stride = boardCols - 1;
  const maxR = boardRows - 2;
  const maxC = boardCols - 2;

  if (o === 0) {
    if ((r === eR - 1 || r === eR) && c >= eC - 2 && c <= eC + 1) return true;
    if ((r === pR - 1 || r === pR) && c >= pC - 2 && c <= pC + 1) return true;
    if (c === 0 || c === maxC) return true;
  } else {
    if ((c === eC - 1 || c === eC) && r >= eR - 2 && r <= eR + 1) return true;
    if ((c === pC - 1 || c === pC) && r >= pR - 2 && r <= pR + 1) return true;
  }

  if (totalWallsPlaced > 0) {
    if (o === 0) {
      if (c >= 2 && hWalls[r * stride + (c - 2)]) return true;
      if (c + 2 <= maxC && hWalls[r * stride + (c + 2)]) return true;
      if (c >= 3 && hWalls[r * stride + (c - 3)]) return true;
      if (c + 3 <= maxC && hWalls[r * stride + (c + 3)]) return true;
    } else {
      if (r >= 2 && vWalls[(r - 2) * stride + c]) return true;
      if (r + 2 <= maxR && vWalls[(r + 2) * stride + c]) return true;
      if (r >= 3 && vWalls[(r - 3) * stride + c]) return true;
      if (r + 3 <= maxR && vWalls[(r + 3) * stride + c]) return true;
    }
    for (let dr = -2; dr <= 2; dr++) {
      for (let dc = -2; dc <= 2; dc++) {
        const nr = r + dr, nc = c + dc;
        if (nr >= 0 && nr <= maxR && nc >= 0 && nc <= maxC) {
          const nIdx = nr * stride + nc;
          if (hWalls[nIdx] || vWalls[nIdx]) return true;
        }
      }
    }
  }
  return false;
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

function computeGoalMetrics(goalRow, outDist, outWays, outExits) {
  const total = boardRows * boardCols;
  outDist.fill(-1, 0, total);
  outWays.fill(0, 0, total);
  outExits.fill(0, 0, total);

  let head = 0, tail = 0;
  const baseGoal = goalRow * boardCols;
  for (let c = 0; c < boardCols; c++) {
    const idx = baseGoal + c;
    outDist[idx] = 0;
    outWays[idx] = 1;
    bfsQ[tail++] = idx;
  }

  while (head < tail) {
    const idx = bfsQ[head++];
    const r = (idx / boardCols) | 0;
    const c = idx - r * boardCols;
    const nd = outDist[idx] + 1;
    const w = outWays[idx];

    if (canUp(r, c)) {
      const ni = idx - boardCols;
      if (outDist[ni] === -1) { outDist[ni] = nd; outWays[ni] = w; bfsQ[tail++] = ni; }
      else if (outDist[ni] === nd) { outWays[ni] = Math.min(4096, outWays[ni] + w); }
    }
    if (canDown(r, c)) {
      const ni = idx + boardCols;
      if (outDist[ni] === -1) { outDist[ni] = nd; outWays[ni] = w; bfsQ[tail++] = ni; }
      else if (outDist[ni] === nd) { outWays[ni] = Math.min(4096, outWays[ni] + w); }
    }
    if (canLeft(r, c)) {
      const ni = idx - 1;
      if (outDist[ni] === -1) { outDist[ni] = nd; outWays[ni] = w; bfsQ[tail++] = ni; }
      else if (outDist[ni] === nd) { outWays[ni] = Math.min(4096, outWays[ni] + w); }
    }
    if (canRight(r, c)) {
      const ni = idx + 1;
      if (outDist[ni] === -1) { outDist[ni] = nd; outWays[ni] = w; bfsQ[tail++] = ni; }
      else if (outDist[ni] === nd) { outWays[ni] = Math.min(4096, outWays[ni] + w); }
    }
  }

  for (let idx = 0; idx < total; idx++) {
    const d = outDist[idx];
    if (d <= 0) continue;
    const r = (idx / boardCols) | 0;
    const c = idx - r * boardCols;
    const target = d - 1;
    let ex = 0;
    if (canUp(r, c) && outDist[idx - boardCols] === target) ex++;
    if (canDown(r, c) && outDist[idx + boardCols] === target) ex++;
    if (canLeft(r, c) && outDist[idx - 1] === target) ex++;
    if (canRight(r, c) && outDist[idx + 1] === target) ex++;
    outExits[idx] = ex;
  }
}

function updateDistMaps() {
  computeGoalMetrics(0, distMe, waysMe, exitsMe);
  if (isRaceMode) {
    distOpp.set(distMe);
    waysOpp.set(waysMe);
    exitsOpp.set(exitsMe);
  } else {
    computeGoalMetrics(boardRows - 1, distOpp, waysOpp, exitsOpp);
  }
}

const DR = [-1, 1, 0, 0];
const DC = [0, 0, -1, 1];

function generatePawnStepsFast(pR, pC, oR, oC, outBuf) {
  let cnt = 0;
  for (let d = 0; d < 4; d++) {
    if (!canStepDir(pR, pC, d)) continue;
    const nr = pR + DR[d], nc = pC + DC[d];
    if (nr === oR && nc === oC) {
      if (canStepDir(oR, oC, d)) {
        outBuf[cnt++] = (oR + DR[d]) * boardCols + (oC + DC[d]);
      } else {
        if (d < 2) {
          if (canLeft(oR, oC)) outBuf[cnt++] = oR * boardCols + (oC - 1);
          if (canRight(oR, oC)) outBuf[cnt++] = oR * boardCols + (oC + 1);
        } else {
          if (canUp(oR, oC)) outBuf[cnt++] = (oR - 1) * boardCols + oC;
          if (canDown(oR, oC)) outBuf[cnt++] = (oR + 1) * boardCols + oC;
        }
      }
    } else {
      outBuf[cnt++] = nr * boardCols + nc;
    }
  }
  return cnt;
}

function evaluate2P(sideToMoveIsMe) {
  const oppGoal = isRaceMode ? 0 : boardRows - 1;
  if (myR === 0) return sideToMoveIsMe ? 100000 : -100000;
  if (oppR === oppGoal) return sideToMoveIsMe ? -100000 : 100000;

  updateDistMaps();
  const myIdx = myR * boardCols + myC;
  const oppIdx = oppR * boardCols + oppC;
  const myDist = distMe[myIdx];
  const oppDist = distOpp[oppIdx];

  if (myDist < 0) return sideToMoveIsMe ? -100000 : 100000;
  if (oppDist < 0) return sideToMoveIsMe ? 100000 : -100000;

  if (myWalls === 0 && oppWalls === 0) {
    let diff = (oppDist - myDist);
    let s = diff * 1000 + (sideToMoveIsMe ? 500 : -500);
    s += (myDist < oppDist || (myDist === oppDist && sideToMoveIsMe)) ? 25000 : -25000;
    return sideToMoveIsMe ? s : -s;
  }

  let score = (oppDist - myDist) * 1000 + (sideToMoveIsMe ? 500 : -500);

  const minDist = Math.min(myDist, oppDist);
  const wallScale = minDist <= 2 ? 0.45 : (minDist <= 4 ? 0.72 : 1.0);
  const mw = Math.min(15, Math.max(0, myWalls));
  const ow = Math.min(15, Math.max(0, oppWalls));
  score += ((WALL_VALUE_TABLE[mw] - WALL_VALUE_TABLE[ow]) * wallScale) | 0;

  score += (exitsMe[myIdx] - exitsOpp[oppIdx]) * 170;
  if (exitsOpp[oppIdx] === 1 && myWalls > 0) score += 410;
  if (exitsMe[myIdx] === 1 && oppWalls > 0) score -= 420;

  return sideToMoveIsMe ? score : -score;
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

function sortSubArray(codes, prios, count) {
  for (let i = 1; i < count; i++) {
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
}

function generateMoves2P(isMe, ply, ttBestCode, prevMove, qSearchOnly) {
  const pR = isMe ? myR : oppR;
  const pC = isMe ? myC : oppC;
  const eR = isMe ? oppR : myR;
  const eC = isMe ? oppC : myC;
  const pWalls = isMe ? myWalls : oppWalls;
  const eWalls = isMe ? oppWalls : myWalls;
  const pGoal = isMe ? 0 : (isRaceMode ? 0 : boardRows - 1);
  const sideIdx = isMe ? 0 : 1;

  updateDistMaps();
  const pDist = isMe ? distMe : distOpp;
  const eDist = isMe ? distOpp : distMe;

  const pIdx = pR * boardCols + pC;
  const eIdx = eR * boardCols + eC;
  const curP = pDist[pIdx];
  const curE = eDist[eIdx];

  const cm = prevMove >= 0 ? counterMoves[sideIdx][prevMove & 2047] : 0;
  const outCodes = plyMoveCodes[ply];
  const outPrios = plyMovePrios[ply];
  let moveCount = 0;

  const nSteps = generatePawnStepsFast(pR, pC, eR, eC, stepBuf);
  for (let i = 0; i < nSteps; i++) {
    const cell = stepBuf[i];
    const sr = (cell / boardCols) | 0;
    const sc = cell - sr * boardCols;
    const code = packMove(0, sr, sc, 0);
    if (sr === pGoal) {
      outCodes[0] = code;
      return 1;
    }
    const newD = pDist[cell];
    const stepGain = curP - newD;
    if (qSearchOnly && stepGain < 2 && newD > 1) continue;

    let prio = stepGain * 16000 + history[sideIdx][code];
    if (code === ttBestCode) prio += 60000000;
    if (code === cm) prio += 15000;
    outCodes[moveCount] = code;
    outPrios[moveCount] = prio;
    moveCount++;
  }

  if (pWalls <= 0) {
    sortSubArray(outCodes, outPrios, moveCount);
    return moveCount;
  }

  const maxR = boardRows - 2;
  const maxC = boardCols - 2;
  let wCount = 0;

  for (let r = 0; r <= maxR; r++) {
    for (let c = 0; c <= maxC; c++) {
      for (let o = 0; o < 2; o++) {
        if (!wallGeometryLegal(r, c, o)) continue;
        if (!isNemesisProbableWall(r, c, o, pR, pC, eR, eC)) continue;

        placeWallFast(r, c, o);
        updateDistMaps();
        const nPDist = isMe ? distMe : distOpp;
        const nEDist = isMe ? distOpp : distMe;
        const newP = nPDist[pIdx];
        const newE = nEDist[eIdx];

        if (newP < 0 || newE < 0) {
          removeWallFast(r, c, o);
          continue;
        }

        const eGain = newE - curE;
        const net = eGain - (newP - curP);
        removeWallFast(r, c, o);

        if (eWalls === 0 && eGain <= 0) continue;
        if (net < 0 && !qSearchOnly) continue;

        const code = packMove(1, r, c, o);
        let prio = net * 10500 + eGain * 3500 + history[sideIdx][code];
        if (code === ttBestCode) prio += 60000000;
        tempWallCodes[wCount] = code;
        tempWallPrios[wCount] = prio;
        wCount++;
      }
    }
  }

  sortSubArray(tempWallCodes, tempWallPrios, wCount);
  const take = Math.min(qSearchOnly ? 6 : 16, wCount);
  for (let i = 0; i < take; i++) {
    outCodes[moveCount] = tempWallCodes[i];
    outPrios[moveCount] = tempWallPrios[i];
    moveCount++;
  }

  sortSubArray(outCodes, outPrios, moveCount);
  return moveCount;
}

function probeTT(idx, keyLo, keyHi) {
  return (ttFlag[idx] !== 0 && ttKeyLo[idx] === keyLo && ttKeyHi[idx] === keyHi);
}

function pvs2P(depth, ply, alpha, beta, sideToMoveIsMe, prevMove) {
  nodes++;
  if ((nodes & 127) === 0 && now() >= deadline) {
    timedOut = true;
    return 0;
  }

  const oppGoal = isRaceMode ? 0 : boardRows - 1;
  if (myR === 0) return sideToMoveIsMe ? (100000 - ply) : -(100000 - ply);
  if (oppR === oppGoal) return sideToMoveIsMe ? -(100000 - ply) : (100000 - ply);

  if (depth <= 0 || ply >= 60) return evaluate2P(sideToMoveIsMe);

  const meIdx = myR * boardCols + myC;
  const oppIdx = oppR * boardCols + oppC;
  const kLo = (wHashLo ^ Z_ME_LO[meIdx] ^ Z_OPP_LO[oppIdx] ^ Z_MW_LO[myWalls] ^ Z_OW_LO[oppWalls]) >>> 0;
  const kHi = (wHashHi ^ Z_ME_HI[meIdx] ^ Z_OPP_HI[oppIdx] ^ Z_MW_HI[myWalls] ^ Z_OW_HI[oppWalls] ^ (sideToMoveIsMe ? 0x12345678 : 0)) >>> 0;
  const ttIdx = (kLo ^ kHi) & TT_MASK;

  let ttBestCode = -1;
  if (probeTT(ttIdx, kLo, kHi)) {
    ttBestCode = ttBestMove[ttIdx];
    if (ttDepth[ttIdx] >= depth) {
      ttHits++;
      if (ttFlag[ttIdx] === 1) return ttScore[ttIdx];
      if (ttFlag[ttIdx] === 2 && ttScore[ttIdx] >= beta) return ttScore[ttIdx];
      if (ttFlag[ttIdx] === 3 && ttScore[ttIdx] <= alpha) return ttScore[ttIdx];
    }
  }

  const alphaOrig = alpha;
  const nMoves = generateMoves2P(sideToMoveIsMe, ply, ttBestCode, prevMove, false);
  if (nMoves === 0) return evaluate2P(sideToMoveIsMe);

  const codes = plyMoveCodes[ply];
  let bestScore = -200000;
  let bestMoveCode = codes[0];
  const sideIdx = sideToMoveIsMe ? 0 : 1;

  for (let i = 0; i < nMoves; i++) {
    const code = codes[i];
    const mType = code & 1;
    const mO = (code >>> 1) & 1;
    const mR = (code >>> 2) & 15;
    const mC = (code >>> 6) & 15;

    const savedR = sideToMoveIsMe ? myR : oppR;
    const savedC = sideToMoveIsMe ? myC : oppC;

    if (mType === 0) {
      if (sideToMoveIsMe) { myR = mR; myC = mC; }
      else { oppR = mR; oppC = mC; }
    } else {
      placeWallFast(mR, mC, mO);
      if (sideToMoveIsMe) myWalls--; else oppWalls--;
    }

    let score;
    if (i === 0) {
      score = -pvs2P(depth - 1, ply + 1, -beta, -alpha, !sideToMoveIsMe, code);
    } else {
      score = -pvs2P(depth - 1, ply + 1, -alpha - 1, -alpha, !sideToMoveIsMe, code);
      if (!timedOut && score > alpha && score < beta) {
        score = -pvs2P(depth - 1, ply + 1, -beta, -alpha, !sideToMoveIsMe, code);
      }
    }

    if (mType === 0) {
      if (sideToMoveIsMe) { myR = savedR; myC = savedC; }
      else { oppR = savedR; oppC = savedC; }
    } else {
      removeWallFast(mR, mC, mO);
      if (sideToMoveIsMe) myWalls++; else oppWalls++;
    }

    if (timedOut) return 0;
    if (score > bestScore) {
      bestScore = score;
      bestMoveCode = code;
    }
    if (score > alpha) alpha = score;
    if (alpha >= beta) {
      cutoffs++;
      history[sideIdx][code] = Math.min(400000, history[sideIdx][code] + depth * depth * 90);
      break;
    }
  }

  let flag = 1;
  if (bestScore <= alphaOrig) flag = 3;
  else if (bestScore >= beta) flag = 2;

  ttKeyLo[ttIdx] = kLo;
  ttKeyHi[ttIdx] = kHi;
  ttScore[ttIdx] = bestScore;
  ttDepth[ttIdx] = depth;
  ttFlag[ttIdx] = flag;
  ttBestMove[ttIdx] = bestMoveCode;

  return bestScore;
}

function searchBestMoveJS(timeBudgetMs, maxSearchDepth) {
  ttFlag.fill(0);
  nodes = 0; ttHits = 0; cutoffs = 0; timedOut = false; completedDepth = 0;
  deadline = now() + timeBudgetMs;

  const nRoot = generateMoves2P(true, 0, -1, -1, false);
  if (nRoot === 0) return null;

  const rootList = new Int32Array(nRoot);
  for (let i = 0; i < nRoot; i++) rootList[i] = plyMoveCodes[0][i];

  if (myWalls === 0 && oppWalls === 0) {
    completedDepth = 1;
    return unpackMove(rootList[0]);
  }

  let bestCode = rootList[0];
  let prevScore = evaluate2P(true);

  for (let depth = 1; depth <= maxSearchDepth; depth++) {
    if (now() >= deadline) break;
    timedOut = false;

    let delta = 700;
    let alpha = (depth >= 3) ? Math.max(-200000, prevScore - delta) : -200000;
    let beta  = (depth >= 3) ? Math.min(200000, prevScore + delta)  : 200000;

    let iterBestCode = bestCode;
    let iterBestScore = -200000;

    for (let i = 0; i < nRoot; i++) {
      const code = rootList[i];
      const mType = code & 1, mO = (code >>> 1) & 1, mR = (code >>> 2) & 15, mC = (code >>> 6) & 15;
      const savedR = myR, savedC = myC;
      if (mType === 0) { myR = mR; myC = mC; }
      else { placeWallFast(mR, mC, mO); myWalls--; }

      const score = -pvs2P(depth - 1, 1, -beta, -alpha, false, code);

      if (mType === 0) { myR = savedR; myC = savedC; }
      else { removeWallFast(mR, mC, mO); myWalls++; }

      if (timedOut) break;
      if (score > iterBestScore) {
        iterBestScore = score;
        iterBestCode = code;
      }
      if (score > alpha) alpha = score;
    }

    if (!timedOut) {
      bestCode = iterBestCode;
      prevScore = iterBestScore;
      completedDepth = depth;
      if (iterBestScore >= 90000) break;
    } else {
      break;
    }
  }
  return unpackMove(bestCode);
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
      self.postMessage({ type: "ready", engine: engineType });
      return;
    }
    if (m.type !== "search") return;

    boardRows = Number(m.rows) || 9;
    boardCols = Number(m.cols) || 9;
    isQuadMode = (m.mode === "quad" || boardCols === 11);
    isRaceMode = (!isQuadMode && boardRows === 13);

    const budget = Math.max(500, Math.min(1800, Number(m.timeMs) || 1200));
    const maxD = Math.min(16, Number(m.maxDepth) || 14);
    const t0 = now();

    let bestMove = null;
    let usedEngine = "js";

    if (wasmReady && wasmSearchFn) {
      const modeCode = isQuadMode ? 2 : (isRaceMode ? 1 : 0);
      const wallStr = Array.isArray(m.wallList) ? m.wallList.join(";") + ";" : "";
      let quadStr = "";
      if (isQuadMode && m.players) {
        const order = ["me", "left", "top", "right"];
        quadStr = order.map(k => {
          const p = m.players[k];
          return `${p.r},${p.c},${p.walls},${p.active ? 1 : 0}`;
        }).join(";") + ";";
      }
      const packed = wasmSearchFn(
        modeCode, boardRows, boardCols,
        m.my.r, m.my.c, m.my.walls,
        m.opp.r, m.opp.c, m.opp.walls,
        wallStr, quadStr, budget, maxD
      );
      if (packed > 0) {
        bestMove = unpackMove(packed);
        nodes = wasmNodesFn ? wasmNodesFn() : 0;
        completedDepth = wasmDepthFn ? wasmDepthFn() : 0;
        usedEngine = "wasm";
      }
    }

    if (!bestMove) {
      loadBoardWalls(m);
      myR = m.my.r; myC = m.my.c; myWalls = m.my.walls;
      oppR = m.opp.r; oppC = m.opp.c; oppWalls = m.opp.walls;
      bestMove = searchBestMoveJS(budget, maxD);
      usedEngine = "js";
    }

    const elapsed = Math.round(now() - t0);
    self.postMessage({
      type: "result",
      id: m.id,
      move: bestMove,
      engine: usedEngine,
      nodes: nodes,
      depth: completedDepth,
      elapsed: elapsed,
      ttHits: ttHits,
      cutoffs: cutoffs
    });
  } catch (err) {
    self.postMessage({
      type: "error",
      id: m.id,
      message: String((err && err.stack) || err)
    });
  }
};
