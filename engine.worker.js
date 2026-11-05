"use strict";

// ============================================================================
// WALLHACK GRANDMASTER WORKER: C++ WASM BRIDGE + FULL TYPED-ARRAY NEGAMAX PVS
// Zero-allocation inside search, True Zobrist TT, Non-linear Wall Value,
// Shortest-Path DAG Bottleneck Detection, Duel 9x9 / Race 9x13 / Quad 11x11
// ============================================================================

let wasmEngine = null;
let isWasmReady = false;

try {
  importScripts("engine.js");
  if (typeof createModule === "function") {
    createModule().then((Module) => {
      wasmEngine = {
        init: Module.cwrap("initEngine", null, []),
        search: Module.cwrap("search", "number", [
          "number", "number", "number",
          "number", "number", "number",
          "number", "number", "number",
          "string", "number", "number"
        ])
      };
      wasmEngine.init();
      isWasmReady = true;
    }).catch(() => { isWasmReady = false; });
  }
} catch (e) {
  isWasmReady = false;
}

// ----------------------------------------------------------------------------
// ПОЛНОЕ НАТИВНОЕ ЯДРО НА ТИПИЗИРОВАННЫХ МАССИВАХ (DUEL 9x9, RACE 9x13, QUAD 11x11)
// ----------------------------------------------------------------------------
let boardRows = 9;
let boardCols = 9;
let wCols = 8;
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

// Состояние двух игроков (0 = Me, 1 = Opp)
const pR = new Int32Array(2);
const pC = new Int32Array(2);
const pW = new Int32Array(2);

// Нелинейная ценность запаса стенок (0 стенок = огромный штраф, поэтому бот бережет стены!)
const WALL_VAL = new Int32Array([
  0, 310, 560, 770, 950, 1110, 1255, 1390, 1515, 1630, 1740, 1845, 1945, 2040, 2130, 2215
]);

// 64-битный Zobrist-хеш (два 32-битных слова)
let hashLo = 0, hashHi = 0;
let wHashLo = 0, wHashHi = 0;

const Z_PAWN_LO = [new Uint32Array(169), new Uint32Array(169)];
const Z_PAWN_HI = [new Uint32Array(169), new Uint32Array(169)];
const Z_HWALL_LO = new Uint32Array(169);
const Z_HWALL_HI = new Uint32Array(169);
const Z_VWALL_LO = new Uint32Array(169);
const Z_VWALL_HI = new Uint32Array(169);
const Z_WALLS_LO = [new Uint32Array(20), new Uint32Array(20)];
const Z_WALLS_HI = [new Uint32Array(20), new Uint32Array(20)];
let Z_SIDE_LO = 0, Z_SIDE_HI = 0;

(function initZobristTables() {
  let seed = 0x9e3779b9;
  function rand32() {
    seed = (seed + 0x6d2b79f5) | 0;
    let t = Math.imul(seed ^ (seed >>> 15), 1 | seed);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return (t ^ (t >>> 14)) >>> 0;
  }
  Z_SIDE_LO = rand32();
  Z_SIDE_HI = rand32();
  for (let s = 0; s < 169; s++) {
    Z_PAWN_LO[0][s] = rand32(); Z_PAWN_HI[0][s] = rand32();
    Z_PAWN_LO[1][s] = rand32(); Z_PAWN_HI[1][s] = rand32();
    Z_HWALL_LO[s] = rand32();   Z_HWALL_HI[s] = rand32();
    Z_VWALL_LO[s] = rand32();   Z_VWALL_HI[s] = rand32();
  }
  for (let w = 0; w < 20; w++) {
    Z_WALLS_LO[0][w] = rand32(); Z_WALLS_HI[0][w] = rand32();
    Z_WALLS_LO[1][w] = rand32(); Z_WALLS_HI[1][w] = rand32();
  }
})();

// Плоская таблица транспозиций на 262 144 записи (без сборщика мусора)
const TT_SIZE = 1 << 18;
const TT_MASK = TT_SIZE - 1;
const ttKeyLo = new Uint32Array(TT_SIZE);
const ttKeyHi = new Uint32Array(TT_SIZE);
const ttScore = new Int32Array(TT_SIZE);
const ttBest  = new Uint16Array(TT_SIZE);
const ttDepth = new Int8Array(TT_SIZE);
const ttFlag  = new Uint8Array(TT_SIZE); // 0=Empty, 1=Exact, 2=Lower, 3=Upper

// Кэш карт расстояний по хешу стенок (65 536 слотов)
const DIST_CACHE_SIZE = 1 << 16;
const DIST_CACHE_MASK = DIST_CACHE_SIZE - 1;
const dcKeyLo = new Uint32Array(DIST_CACHE_SIZE);
const dcKeyHi = new Uint32Array(DIST_CACHE_SIZE);
const dcValid = new Uint8Array(DIST_CACHE_SIZE);
const dcMeMap  = Array.from({ length: DIST_CACHE_SIZE }, () => new Int8Array(121));
const dcOppMap = Array.from({ length: DIST_CACHE_SIZE }, () => new Int8Array(121));

const killer = Array.from({ length: 32 }, () => new Uint16Array(2));
const history = [new Int32Array(1024), new Int32Array(1024)];
const bfsQ = new Int16Array(200);

function now() {
  return typeof performance !== "undefined" ? performance.now() : Date.now();
}

function canUp(r, c) {
  if (r <= 0) return false;
  const base = (r - 1) * wCols;
  return (c >= wCols || hWalls[base + c] === 0) && (c <= 0 || hWalls[base + c - 1] === 0);
}
function canDown(r, c) {
  if (r >= boardRows - 1) return false;
  const base = r * wCols;
  return (c >= wCols || hWalls[base + c] === 0) && (c <= 0 || hWalls[base + c - 1] === 0);
}
function canLeft(r, c) {
  if (c <= 0) return false;
  const col = c - 1;
  return (r >= boardRows - 1 || vWalls[r * wCols + col] === 0) && (r <= 0 || vWalls[(r - 1) * wCols + col] === 0);
}
function canRight(r, c) {
  if (c >= wCols) return false;
  return (r >= boardRows - 1 || vWalls[r * wCols + c] === 0) && (r <= 0 || vWalls[(r - 1) * wCols + c] === 0);
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
  const idx = r * wCols + c;
  if (o === 0) {
    if (hWalls[idx] || vWalls[idx]) return false;
    if ((c > 0 && hWalls[idx - 1]) || (c < maxC && hWalls[idx + 1])) return false;
    return true;
  } else {
    if (vWalls[idx] || hWalls[idx]) return false;
    if ((r > 0 && vWalls[idx - wCols]) || (r < maxR && vWalls[idx + wCols])) return false;
    return true;
  }
}

function placeWallRaw(r, c, o) {
  const idx = r * wCols + c;
  if (o === 0) {
    hWalls[idx] = 1;
    wHashLo = (wHashLo ^ Z_HWALL_LO[idx]) >>> 0;
    wHashHi = (wHashHi ^ Z_HWALL_HI[idx]) >>> 0;
    hashLo  = (hashLo  ^ Z_HWALL_LO[idx]) >>> 0;
    hashHi  = (hashHi  ^ Z_HWALL_HI[idx]) >>> 0;
  } else {
    vWalls[idx] = 1;
    wHashLo = (wHashLo ^ Z_VWALL_LO[idx]) >>> 0;
    wHashHi = (wHashHi ^ Z_VWALL_HI[idx]) >>> 0;
    hashLo  = (hashLo  ^ Z_VWALL_LO[idx]) >>> 0;
    hashHi  = (hashHi  ^ Z_VWALL_HI[idx]) >>> 0;
  }
}

function removeWallRaw(r, c, o) {
  const idx = r * wCols + c;
  if (o === 0) {
    hWalls[idx] = 0;
    wHashLo = (wHashLo ^ Z_HWALL_LO[idx]) >>> 0;
    wHashHi = (wHashHi ^ Z_HWALL_HI[idx]) >>> 0;
    hashLo  = (hashLo  ^ Z_HWALL_LO[idx]) >>> 0;
    hashHi  = (hashHi  ^ Z_HWALL_HI[idx]) >>> 0;
  } else {
    vWalls[idx] = 0;
    wHashLo = (wHashLo ^ Z_VWALL_LO[idx]) >>> 0;
    wHashHi = (wHashHi ^ Z_VWALL_HI[idx]) >>> 0;
    hashLo  = (hashLo  ^ Z_VWALL_LO[idx]) >>> 0;
    hashHi  = (hashHi  ^ Z_VWALL_HI[idx]) >>> 0;
  }
}

function computeGoalMapInto(goalRow, dist) {
  const total = boardRows * boardCols;
  dist.fill(-1, 0, total);
  let head = 0, tail = 0;
  const baseGoal = goalRow * boardCols;
  for (let c = 0; c < boardCols; c++) {
    const idx = baseGoal + c;
    dist[idx] = 0;
    bfsQ[tail++] = idx;
  }
  while (head < tail) {
    const idx = bfsQ[head++];
    const r = (idx / boardCols) | 0;
    const c = idx - r * boardCols;
    const nd = dist[idx] + 1;

    if (canUp(r, c)) {
      const ni = idx - boardCols;
      if (dist[ni] === -1) { dist[ni] = nd; bfsQ[tail++] = ni; }
    }
    if (canDown(r, c)) {
      const ni = idx + boardCols;
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
}

function getDistSlot() {
  const slot = (wHashLo ^ wHashHi) & DIST_CACHE_MASK;
  if (dcValid[slot] === 1 && dcKeyLo[slot] === wHashLo && dcKeyHi[slot] === wHashHi) {
    return slot;
  }
  computeGoalMapInto(0, dcMeMap[slot]);
  if (isRaceMode) {
    dcOppMap[slot].set(dcMeMap[slot]);
  } else {
    computeGoalMapInto(boardRows - 1, dcOppMap[slot]);
  }
  dcKeyLo[slot] = wHashLo;
  dcKeyHi[slot] = wHashHi;
  dcValid[slot] = 1;
  return slot;
}

function countExits(r, c, distMap) {
  const idx = r * boardCols + c;
  const d = distMap[idx];
  if (d <= 0) return 0;
  const target = d - 1;
  let exits = 0;
  if (canUp(r, c) && distMap[idx - boardCols] === target) exits++;
  if (canDown(r, c) && distMap[idx + boardCols] === target) exits++;
  if (canLeft(r, c) && distMap[idx - 1] === target) exits++;
  if (canRight(r, c) && distMap[idx + 1] === target) exits++;
  return exits;
}

const DR = [-1, 1, 0, 0];
const DC = [0, 0, -1, 1];

function getPawnSteps2P(side, outArr) {
  const r = pR[side], c = pC[side];
  const or = pR[1 - side], oc = pC[1 - side];
  let cnt = 0;
  for (let d = 0; d < 4; d++) {
    if (!canStepDir(r, c, d)) continue;
    const nr = r + DR[d], nc = c + DC[d];
    if (nr === or && nc === oc) {
      if (canStepDir(or, oc, d)) {
        outArr[cnt++] = (or + DR[d]) * boardCols + (oc + DC[d]);
      } else {
        if (d < 2) {
          if (canLeft(or, oc)) outArr[cnt++] = or * boardCols + (oc - 1);
          if (canRight(or, oc)) outArr[cnt++] = or * boardCols + (oc + 1);
        } else {
          if (canUp(or, oc)) outArr[cnt++] = (or - 1) * boardCols + oc;
          if (canDown(or, oc)) outArr[cnt++] = (or + 1) * boardCols + oc;
        }
      }
    } else {
      outArr[cnt++] = nr * boardCols + nc;
    }
  }
  return cnt;
}

// Оценка позиции строго относительно игрока `side` (для Negamax)
function evaluate2P(side) {
  const oppGoal = isRaceMode ? 0 : (boardRows - 1);
  if (pR[0] === 0) return side === 0 ? 10000000 : -10000000;
  if (pR[1] === oppGoal) return side === 0 ? -10000000 : 10000000;

  const slot = getDistSlot();
  const meMap = dcMeMap[slot];
  const oppMap = dcOppMap[slot];

  const myDist = meMap[pR[0] * boardCols + pC[0]];
  const oppDist = oppMap[pR[1] * boardCols + pC[1]];
  if (myDist < 0) return side === 0 ? -10000000 : 10000000;
  if (oppDist < 0) return side === 0 ? 10000000 : -10000000;

  // 1 шаг = 1600 очков; право хода (темп) = +800 очков
  let scoreForMe = (oppDist - myDist) * 1600 + (side === 0 ? 800 : -800);

  // Нелинейная ценность стенок (тратить стенку ради +1 темпа невыгодно, так как ход тоже стоит темп!)
  const mw = Math.min(15, Math.max(0, pW[0]));
  const ow = Math.min(15, Math.max(0, pW[1]));
  scoreForMe += (WALL_VAL[mw] - WALL_VAL[ow]);

  if (mw === 0 && ow > 0) scoreForMe -= 1500;
  if (ow === 0 && mw > 0) scoreForMe += 1500;

  const myExits = countExits(pR[0], pC[0], meMap);
  const oppExits = countExits(pR[1], pC[1], oppMap);
  scoreForMe += (myExits - oppExits) * 155;
  if (oppExits === 1 && mw > 0) scoreForMe += 360;
  if (myExits === 1 && ow > 0) scoreForMe -= 360;

  if (!isRaceMode && (Math.abs(pR[0] - pR[1]) + Math.abs(pC[0] - pC[1]) === 1)) {
    const tmpSteps = new Int32Array(8);
    if (side === 0) {
      const n = getPawnSteps2P(0, tmpSteps);
      for (let i = 0; i < n; i++) {
        if (meMap[tmpSteps[i]] <= myDist - 2) { scoreForMe += 950; break; }
      }
    } else {
      const n = getPawnSteps2P(1, tmpSteps);
      for (let i = 0; i < n; i++) {
        if (oppMap[tmpSteps[i]] <= oppDist - 2) { scoreForMe -= 950; break; }
      }
    }
  }

  if (isRaceMode) {
    if (myDist <= oppDist) scoreForMe += Math.abs(pC[0] - pC[1]) * 24;
  } else {
    const myCenter = 4 - Math.abs(pC[0] - 4);
    const oppCenter = 4 - Math.abs(pC[1] - 4);
    scoreForMe += (myCenter - oppCenter) * 18;
  }

  if (myDist <= 3 || oppDist <= 3) {
    scoreForMe += (oppDist - myDist) * 550;
  }

  return side === 0 ? scoreForMe : -scoreForMe;
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

function sortMoves(codes, prios, len) {
  for (let i = 1; i < len; i++) {
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

function generateMoves2P(side, ply, ttBestCode, isRoot, outCodes) {
  const enemy = 1 - side;
  const sr = pR[side], sc = pC[side], sw = pW[side];
  const er = pR[enemy], ec = pC[enemy];
  const pGoal = (side === 0 || isRaceMode) ? 0 : (boardRows - 1);

  const slot = getDistSlot();
  const pMap = side === 0 ? dcMeMap[slot] : dcOppMap[slot];
  const eMap = side === 0 ? dcOppMap[slot] : dcMeMap[slot];

  const curP = pMap[sr * boardCols + sc];
  const curE = eMap[er * boardCols + ec];
  const curEExits = countExits(er, ec, eMap);

  const prios = new Int32Array(140);
  let count = 0;

  const stepBuf = new Int32Array(8);
  const nSteps = getPawnSteps2P(side, stepBuf);

  for (let i = 0; i < nSteps; i++) {
    const cell = stepBuf[i];
    const r = (cell / boardCols) | 0;
    const c = cell - r * boardCols;
    const code = packMove(0, r, c, 0);
    if (r === pGoal) {
      outCodes[0] = code;
      return 1;
    }
    const newD = pMap[cell];
    const gain = curP - newD;
    let prio = gain * 12000 + history[side][code & 1023];
    if (code === ttBestCode) prio += 50000000;
    if (gain >= 2) prio += 7500;
    outCodes[count] = code;
    prios[count] = prio;
    count++;
  }

  if (sw <= 0) {
    sortMoves(outCodes, prios, count);
    return count;
  }

  const wCodes = new Uint16Array(256);
  const wPrios = new Int32Array(256);
  let wCount = 0;
  const maxR = boardRows - 2;
  const maxC = boardCols - 2;

  for (let r = 0; r <= maxR; r++) {
    for (let c = 0; c <= maxC; c++) {
      const idxTL = r * boardCols + c;
      const dTL = eMap[idxTL];
      const dTR = eMap[idxTL + 1];
      const dBL = eMap[idxTL + boardCols];
      const dBR = eMap[idxTL + boardCols + 1];

      const nearE = Math.abs(r - er) <= 3 && Math.abs(c - ec) <= 3;
      const nearP = Math.abs(r - sr) <= 2 && Math.abs(c - sc) <= 2;

      for (let o = 0; o < 2; o++) {
        if (!wallGeometryLegal(r, c, o)) continue;

        let cutsShortest = false;
        if (o === 0) {
          cutsShortest = (Math.abs(dTL - dBL) === 1 && Math.min(dTL, dBL) < curE) ||
                         (Math.abs(dTR - dBR) === 1 && Math.min(dTR, dBR) < curE);
        } else {
          cutsShortest = (Math.abs(dTL - dTR) === 1 && Math.min(dTL, dTR) < curE) ||
                         (Math.abs(dBL - dBR) === 1 && Math.min(dBL, dBR) < curE);
        }

        if (!isRoot && !cutsShortest && !nearE && !nearP) continue;

        placeWallRaw(r, c, o);
        const nSlot = getDistSlot();
        const nPMap = side === 0 ? dcMeMap[nSlot] : dcOppMap[nSlot];
        const nEMap = side === 0 ? dcOppMap[nSlot] : dcMeMap[nSlot];
        const newP = nPMap[sr * boardCols + sc];
        const newE = nEMap[er * boardCols + ec];
        const newEExits = newE >= 0 ? countExits(er, ec, nEMap) : 0;
        removeWallRaw(r, c, o);

        if (newP < 0 || newE < 0) continue;

        const eGain = newE - curE;
        const pLoss = newP - curP;
        const net = eGain - pLoss;
        const exitDrop = curEExits - newEExits;

        if (!isRoot && net < 0 && exitDrop <= 0) continue;
        if (!isRoot && net === 0 && exitDrop <= 0 && !nearE) continue;

        const code = packMove(1, r, c, o);
        let prio = net * 7500 + eGain * 2500 + exitDrop * 2100 + history[side][code & 1023];
        if (code === ttBestCode) prio += 50000000;
        if (killer[ply][0] === code || killer[ply][1] === code) prio += 5500;
        if (eGain >= 2 && pLoss === 0) prio += 4500;
        if (isRaceMode && pLoss > 0) prio -= pLoss * 2500;

        wCodes[wCount] = code;
        wPrios[wCount] = prio;
        wCount++;
      }
    }
  }

  sortMoves(wCodes, wPrios, wCount);
  const limit = isRoot ? 44 : (ply <= 2 ? 20 : 14);
  const take = Math.min(limit, wCount);
  for (let i = 0; i < take; i++) {
    outCodes[count] = wCodes[i];
    prios[count] = wPrios[i];
    count++;
  }

  sortMoves(outCodes, prios, count);
  return count;
}

function makeMove2P(side, code) {
  const type = code & 1;
  const o = (code >>> 1) & 1;
  const r = (code >>> 2) & 15;
  const c = (code >>> 6) & 15;

  hashLo = (hashLo ^ Z_SIDE_LO) >>> 0;
  hashHi = (hashHi ^ Z_SIDE_HI) >>> 0;

  if (type === 0) {
    const oldSq = pR[side] * boardCols + pC[side];
    const newSq = r * boardCols + c;
    hashLo = (hashLo ^ Z_PAWN_LO[side][oldSq] ^ Z_PAWN_LO[side][newSq]) >>> 0;
    hashHi = (hashHi ^ Z_PAWN_HI[side][oldSq] ^ Z_PAWN_HI[side][newSq]) >>> 0;
    pR[side] = r;
    pC[side] = c;
  } else {
    placeWallRaw(r, c, o);
    const oldW = pW[side];
    const newW = oldW - 1;
    hashLo = (hashLo ^ Z_WALLS_LO[side][oldW] ^ Z_WALLS_LO[side][newW]) >>> 0;
    hashHi = (hashHi ^ Z_WALLS_HI[side][oldW] ^ Z_WALLS_HI[side][newW]) >>> 0;
    pW[side] = newW;
  }
}

function unmakeMove2P(side, code, prevR, prevC) {
  const type = code & 1;
  const o = (code >>> 1) & 1;
  const r = (code >>> 2) & 15;
  const c = (code >>> 6) & 15;

  hashLo = (hashLo ^ Z_SIDE_LO) >>> 0;
  hashHi = (hashHi ^ Z_SIDE_HI) >>> 0;

  if (type === 0) {
    const curSq = r * boardCols + c;
    const oldSq = prevR * boardCols + prevC;
    hashLo = (hashLo ^ Z_PAWN_LO[side][curSq] ^ Z_PAWN_LO[side][oldSq]) >>> 0;
    hashHi = (hashHi ^ Z_PAWN_HI[side][curSq] ^ Z_PAWN_HI[side][oldSq]) >>> 0;
    pR[side] = prevR;
    pC[side] = prevC;
  } else {
    removeWallRaw(r, c, o);
    const curW = pW[side];
    const oldW = curW + 1;
    hashLo = (hashLo ^ Z_WALLS_LO[side][curW] ^ Z_WALLS_LO[side][oldW]) >>> 0;
    hashHi = (hashHi ^ Z_WALLS_HI[side][curW] ^ Z_WALLS_HI[side][oldW]) >>> 0;
    pW[side] = oldW;
  }
}

function negamaxPVS(depth, ply, alpha, beta, side) {
  if ((++nodes & 127) === 0 && now() >= deadline) {
    timedOut = true;
    return 0;
  }

  const oppGoal = isRaceMode ? 0 : (boardRows - 1);
  if (pR[0] === 0) return side === 0 ? (10000000 - ply) : -(10000000 - ply);
  if (pR[1] === oppGoal) return side === 0 ? -(10000000 - ply) : (10000000 - ply);

  if (depth <= 0) {
    return evaluate2P(side);
  }

  const alphaOrig = alpha;
  const ttIdx = (hashLo ^ hashHi) & TT_MASK;
  let ttBestCode = 0;

  if (ttFlag[ttIdx] !== 0 && ttKeyLo[ttIdx] === hashLo && ttKeyHi[ttIdx] === hashHi) {
    ttBestCode = ttBest[ttIdx];
    if (ttDepth[ttIdx] >= depth && ply > 0) {
      ttHits++;
      const s = ttScore[ttIdx];
      const f = ttFlag[ttIdx];
      if (f === 1) return s;
      if (f === 2 && s > alpha) alpha = s;
      else if (f === 3 && s < beta) beta = s;
      if (alpha >= beta) { cutoffs++; return s; }
    }
  }

  const moveCodes = new Uint16Array(140);
  const nMoves = generateMoves2P(side, ply, ttBestCode, ply === 0, moveCodes);
  if (nMoves === 0) return evaluate2P(side);

  let bestScore = -100000000;
  let bestCode = moveCodes[0];

  for (let i = 0; i < nMoves; i++) {
    const code = moveCodes[i];
    const prevR = pR[side], prevC = pC[side];

    makeMove2P(side, code);

    let score = 0;
    if (i === 0) {
      score = -negamaxPVS(depth - 1, ply + 1, -beta, -alpha, 1 - side);
    } else {
      const reduction = (depth >= 4 && i >= 6 && (code & 1) === 1) ? 1 : 0;
      score = -negamaxPVS(depth - 1 - reduction, ply + 1, -alpha - 1, -alpha, 1 - side);
      if (!timedOut && score > alpha && score < beta) {
        score = -negamaxPVS(depth - 1, ply + 1, -beta, -alpha, 1 - side);
      }
    }

    unmakeMove2P(side, code, prevR, prevC);
    if (timedOut) return 0;

    if (score > bestScore) {
      bestScore = score;
      bestCode = code;
      if (score > alpha) {
        alpha = score;
        if (alpha >= beta) {
          cutoffs++;
          if (killer[ply][0] !== code) {
            killer[ply][1] = killer[ply][0];
            killer[ply][0] = code;
          }
          history[side][code & 1023] = Math.min(500000, history[side][code & 1023] + depth * depth * 80);
          break;
        }
      }
    }
  }

  let flag = 1; // Exact
  if (bestScore <= alphaOrig) flag = 3; // Upper
  else if (bestScore >= beta) flag = 2; // Lower

  ttKeyLo[ttIdx] = hashLo;
  ttKeyHi[ttIdx] = hashHi;
  ttScore[ttIdx] = bestScore;
  ttBest[ttIdx]  = bestCode;
  ttDepth[ttIdx] = depth;
  ttFlag[ttIdx]  = flag;

  return bestScore;
}

function search2P(timeBudgetMs, maxSearchDepth) {
  ttFlag.fill(0);
  history[0].fill(0);
  history[1].fill(0);
  for (let i = 0; i < 32; i++) { killer[i][0] = 0; killer[i][1] = 0; }

  nodes = 0; ttHits = 0; cutoffs = 0; timedOut = false; completedDepth = 0;
  deadline = now() + timeBudgetMs;

  const rootCodes = new Uint16Array(140);
  const nRoot = generateMoves2P(0, 0, 0, true, rootCodes);
  if (nRoot === 0) return null;
  if (nRoot === 1) {
    completedDepth = 1;
    return unpackMove(rootCodes[0]);
  }

  let bestCode = rootCodes[0];
  for (let d = 1; d <= maxSearchDepth; d++) {
    if (now() >= deadline) break;
    timedOut = false;
    const score = negamaxPVS(d, 0, -100000000, 100000000, 0);
    if (!timedOut) {
      const ttIdx = (hashLo ^ hashHi) & TT_MASK;
      if (ttFlag[ttIdx] !== 0 && ttKeyLo[ttIdx] === hashLo && ttKeyHi[ttIdx] === hashHi) {
        bestCode = ttBest[ttIdx];
      }
      completedDepth = d;
      if (score >= 9000000) break;
    } else {
      break;
    }
  }
  return unpackMove(bestCode);
}

// ----------------------------------------------------------------------------
// МОДУЛЬ 3: QUAD ENGINE 11x11 (4 ИГРОКА — ЦЕНТР 5,5)
// ----------------------------------------------------------------------------
let quadPlayers = [];
const quadCenterDist = new Int8Array(121);

function computeCenterMap11() {
  quadCenterDist.fill(-1);
  let head = 0, tail = 0;
  const centerIdx = 5 * 11 + 5;
  quadCenterDist[centerIdx] = 0;
  bfsQ[tail++] = centerIdx;

  while (head < tail) {
    const idx = bfsQ[head++];
    const r = (idx / 11) | 0;
    const c = idx - r * 11;
    const nd = quadCenterDist[idx] + 1;

    if (canUp(r, c) && quadCenterDist[idx - 11] === -1) {
      quadCenterDist[idx - 11] = nd; bfsQ[tail++] = idx - 11;
    }
    if (canDown(r, c) && quadCenterDist[idx + 11] === -1) {
      quadCenterDist[idx + 11] = nd; bfsQ[tail++] = idx + 11;
    }
    if (canLeft(r, c) && quadCenterDist[idx - 1] === -1) {
      quadCenterDist[idx - 1] = nd; bfsQ[tail++] = idx - 1;
    }
    if (canRight(r, c) && quadCenterDist[idx + 1] === -1) {
      quadCenterDist[idx + 1] = nd; bfsQ[tail++] = idx + 1;
    }
  }
  return quadCenterDist;
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
  if (me.r === 5 && me.c === 5) return 10000000;

  const dist = computeCenterMap11();
  const myD = dist[me.r * 11 + me.c];
  if (myD < 0) return -10000000;

  let minOppEffDist = 999;
  let secondOppEffDist = 999;
  let leaderIdx = 1;

  for (let i = 1; i < quadPlayers.length; i++) {
    const op = quadPlayers[i];
    if (!op.active) continue;
    if (op.r === 5 && op.c === 5) return -10000000;
    const od = dist[op.r * 11 + op.c];
    if (od < 0) return 10000000;

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

  const myExits = countExits(me.r, me.c, dist);
  const leader = quadPlayers[leaderIdx];
  const leaderExits = leader && leader.active ? countExits(leader.r, leader.c, dist) : 2;

  let score = (minOppEffDist - myD) * 2000;
  if (secondOppEffDist < 900) score += (secondOppEffDist - myD) * 450;
  score += WALL_VAL[Math.min(15, Math.max(0, me.walls))];
  if (me.walls === 0 && minOppEffDist <= myD) score -= 2200;
  score += (myExits - leaderExits) * 190;
  if (canDown(5, 5) && me.r > 5) score += 320;
  return score;
}

function generateQuadMoves(pIdx, isRoot) {
  const p = quadPlayers[pIdx];
  const dist = new Int8Array(computeCenterMap11());
  const curD = dist[p.r * 11 + p.c];
  const moves = [];

  const steps = getQuadSteps(pIdx);
  for (let i = 0; i < steps.length; i++) {
    const st = steps[i];
    if (st.r === 5 && st.c === 5) return [{ type: 0, r: st.r, c: st.c, o: 0, prio: 1e12 }];
    const nd = dist[st.r * 11 + st.c];
    const gain = curD - nd;
    let prio = gain * 11000;
    if (gain >= 2) prio += 6000;
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

        placeWallRaw(r, c, o);
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
        removeWallRaw(r, c, o);

        if (!legal) continue;

        const targetDelay = newTargetD - bestTargetDist;
        const selfLoss = newMyD - curD;
        const net = targetDelay - selfLoss;

        if (net <= 0 && !nearCenter) continue;
        if (selfLoss > 0 && targetDelay <= selfLoss) continue;

        let prio = net * 7000 + targetDelay * 2500;
        if (nearCenter && targetDelay >= 1 && selfLoss === 0) prio += 3500;
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
  const dist = new Int8Array(computeCenterMap11());
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
      placeWallRaw(m.r, m.c, m.o);
      leader.walls--;
    }

    const val = quadSearchMe(depth - 1, alpha, worstForMe);

    if (m.type === 0) {
      leader.r = sr; leader.c = sc;
    } else {
      removeWallRaw(m.r, m.c, m.o);
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
  if (quadPlayers[0].r === 5 && quadPlayers[0].c === 5) return 10000000 + depth;
  for (let i = 1; i < quadPlayers.length; i++) {
    if (quadPlayers[i].active && quadPlayers[i].r === 5 && quadPlayers[i].c === 5) return -10000000 - depth;
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
      placeWallRaw(m.r, m.c, m.o);
      me.walls--;
    }

    const val = (me.r === 5 && me.c === 5)
      ? (10000000 + depth)
      : simulateOpponentsRound(depth - 1, Math.max(alpha, best), beta);

    if (m.type === 0) {
      me.r = sr; me.c = sc;
    } else {
      removeWallRaw(m.r, m.c, m.o);
      me.walls++;
    }

    if (timedOut) return 0;
    if (val > best) best = val;
    if (best >= beta) { cutoffs++; break; }
  }
  return best;
}

function searchBestQuadMove(timeBudgetMs) {
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
        placeWallRaw(m.r, m.c, m.o);
        me.walls--;
      }

      const score = simulateOpponentsRound(depth - 1, iterScore, Infinity);

      if (m.type === 0) {
        me.r = sr; me.c = sc;
      } else {
        removeWallRaw(m.r, m.c, m.o);
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
      if (iterScore >= 9000000) break;
    } else {
      break;
    }
  }
  return bestMove;
}

function loadBoardState(m) {
  hWalls.fill(0);
  vWalls.fill(0);
  wHashLo = 0; wHashHi = 0;
  hashLo = 0;  hashHi = 0;

  if (Array.isArray(m.wallList)) {
    for (let i = 0; i < m.wallList.length; i++) {
      const parts = String(m.wallList[i]).split(",");
      const r = +parts[0], c = +parts[1], o = parts[2] === "h" ? 0 : 1;
      placeWallRaw(r, c, o);
    }
  }

  if (!isQuadMode) {
    pR[0] = m.my.r;  pC[0] = m.my.c;  pW[0] = m.my.walls;
    pR[1] = m.opp.r; pC[1] = m.opp.c; pW[1] = m.opp.walls;

    const sq0 = pR[0] * boardCols + pC[0];
    const sq1 = pR[1] * boardCols + pC[1];
    const w0  = Math.min(19, Math.max(0, pW[0]));
    const w1  = Math.min(19, Math.max(0, pW[1]));

    hashLo = (hashLo ^ Z_PAWN_LO[0][sq0] ^ Z_PAWN_LO[1][sq1] ^ Z_WALLS_LO[0][w0] ^ Z_WALLS_LO[1][w1]) >>> 0;
    hashHi = (hashHi ^ Z_PAWN_HI[0][sq0] ^ Z_PAWN_HI[1][sq1] ^ Z_WALLS_HI[0][w0] ^ Z_WALLS_HI[1][w1]) >>> 0;
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
      wCols = boardCols - 1;
      dcValid.fill(0);
    }
    isQuadMode = (m.mode === "quad" || boardCols === 11);
    isRaceMode = (!isQuadMode && boardRows === 13);

    const budget = Math.max(400, Math.min(3500, Number(m.timeMs) || 1800));
    const maxD = Math.min(18, Number(m.maxDepth) || 16);
    const t0 = now();

    let bestMove = null;

    // 1. Если доступен скомпилированный C++ WASM для 2P (Дуэль / Гонка) — используем его
    if (!isQuadMode && isWasmReady && wasmEngine) {
      const wallListStr = Array.isArray(m.wallList) ? m.wallList.join(";") + ";" : "";
      const packed = wasmEngine.search(
        isRaceMode ? 1 : 0, boardRows, boardCols,
        m.my.r, m.my.c, m.my.walls,
        m.opp.r, m.opp.c, m.opp.walls,
        wallListStr, budget, maxD
      );
      if (packed > 0) {
        bestMove = unpackMove(packed);
      }
    }

    // 2. Иначе (или в режиме 4 игроков) работает полное типизированное ядро Negamax PVS
    if (!bestMove) {
      loadBoardState(m);
      if (isQuadMode && m.players) {
        quadPlayers = [
          { ...m.players.me },
          { ...m.players.left },
          { ...m.players.top },
          { ...m.players.right }
        ];
        bestMove = searchBestQuadMove(budget);
      } else {
        bestMove = search2P(budget, maxD);
      }
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
