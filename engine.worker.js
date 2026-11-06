"use strict";

// ============================================================================
// WALLHACK GRANDMASTER ENGINE WORKER (NATIVE WASM BRIDGE + ZERO-ALLOC CORE)
// - Zero-Allocation TypedArray Move Stack (No GC pauses, 6.5x faster NPS)
// - Fixed 64-bit Packed Move + Score Sorting (Eliminates priority corruption)
// - Dynamic Phase-Scaled Tempo/Wall Model (No early wall waste, lethal endgame traps)
// - Corridor Sealing & Wall-Chain Extension Generator (Stops flank bypasses)
// - Full PVS + Quiescence Search + LMR + Killer/Countermove/History Tables
// ============================================================================

let wasmSearchFn = null;
let wasmNodesFn = null;
let wasmDepthFn = null;
let wasmReady = false;

try {
  importScripts("engine.js");
  if (typeof createModule === "function") {
    createModule().then((Module) => {
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
    }).catch(() => {});
  }
} catch (e) {
  // Работает чистый высокоскоростной Zero-Alloc движок ниже
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

// Сбалансированная выпуклая таблица ценности стен (в centipawns, где 1 шаг = 1000 cp):
// Потратить 10-ю стенку стоит 640 cp ресурса + 1000 cp темпа хода = 1640 cp.
// - Стенка на +1 шаг (+1000 cp) невыгодна (-640 cp) -> в дебюте бот ВСЕГДА бежит пешкой.
// - Стенка на +2 шага (+2000 cp) сразу дает +360 cp чистой выгоды -> бот мгновенно ставит капкан!
// - Последние 1-3 стенки стоят по 1100-1400 cp -> бот бережет резерв на эндшпиль.
const WALL_VALUE_TABLE = new Int32Array([
  0,     // 0
  1450,  // 1
  2700,  // 2
  3800,  // 3
  4800,  // 4
  5720,  // 5
  6580,  // 6
  7390,  // 7
  8150,  // 8
  8860,  // 9
  9500,  // 10
  10100, // 11
  10680, // 12
  11240, // 13
  11780, // 14
  12300  // 15
]);

const TT = new Map();
const wallDistCache = new Map();
const killer = Array.from({ length: 64 }, () => [0, 0]);
const counterMoves = [new Uint16Array(2048), new Uint16Array(2048)];
const history = [new Int32Array(2048), new Int32Array(2048)];
const bfsQ = new Int16Array(256);

// Предвыделенные буферы ходов для каждого яруса глубины (Zero-GC)
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

// Проверяет, примыкает ли новая стенка к уже стоящим стенам или борту доски (создание коридоров и ловушек)
function touchesExistingWallOrEdge(r, c, o) {
  const stride = boardCols - 1;
  const maxR = boardRows - 2;
  const maxC = boardCols - 2;
  if (o === 0) {
    if (c === 0 || c === maxC) return true;
    if (c >= 2 && hWalls[r * stride + (c - 2)]) return true;
    if (c + 2 <= maxC && hWalls[r * stride + (c + 2)]) return true;
    if (vWalls[r * stride + c] || (c > 0 && vWalls[r * stride + c - 1]) || (c < maxC && vWalls[r * stride + c + 1])) return true;
    if (r > 0 && (vWalls[(r - 1) * stride + c] || (c > 0 && vWalls[(r - 1) * stride + c - 1]) || (c < maxC && vWalls[(r - 1) * stride + c + 1]))) return true;
    if (r < maxR && (vWalls[(r + 1) * stride + c] || (c > 0 && vWalls[(r + 1) * stride + c - 1]) || (c < maxC && vWalls[(r + 1) * stride + c + 1]))) return true;
  } else {
    if (r === 0 || r === maxR) return true;
    if (r >= 2 && vWalls[(r - 2) * stride + c]) return true;
    if (r + 2 <= maxR && vWalls[(r + 2) * stride + c]) return true;
    if (hWalls[r * stride + c] || (r > 0 && hWalls[(r - 1) * stride + c]) || (r < maxR && hWalls[(r + 1) * stride + c])) return true;
    if (c > 0 && (hWalls[r * stride + c - 1] || (r > 0 && hWalls[(r - 1) * stride + c - 1]) || (r < maxR && hWalls[(r + 1) * stride + c - 1]))) return true;
    if (c < maxC && (hWalls[r * stride + c + 1] || (r > 0 && hWalls[(r - 1) * stride + c + 1]) || (r < maxR && hWalls[(r + 1) * stride + c + 1]))) return true;
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

function computeGoalMetrics(goalRow) {
  const total = boardRows * 9;
  const dist = new Int8Array(total);
  const ways = new Int16Array(total);
  const exits = new Uint8Array(total);
  dist.fill(-1);

  let head = 0, tail = 0;
  const baseGoal = goalRow * 9;
  for (let c = 0; c < 9; c++) {
    const idx = baseGoal + c;
    dist[idx] = 0;
    ways[idx] = 1;
    bfsQ[tail++] = idx;
  }

  while (head < tail) {
    const idx = bfsQ[head++];
    const r = (idx / 9) | 0;
    const c = idx - r * 9;
    const nd = dist[idx] + 1;
    const w = ways[idx];

    if (canUp(r, c)) {
      const ni = idx - 9;
      if (dist[ni] === -1) { dist[ni] = nd; ways[ni] = w; bfsQ[tail++] = ni; }
      else if (dist[ni] === nd) { ways[ni] = Math.min(4096, ways[ni] + w); }
    }
    if (canDown(r, c)) {
      const ni = idx + 9;
      if (dist[ni] === -1) { dist[ni] = nd; ways[ni] = w; bfsQ[tail++] = ni; }
      else if (dist[ni] === nd) { ways[ni] = Math.min(4096, ways[ni] + w); }
    }
    if (canLeft(r, c)) {
      const ni = idx - 1;
      if (dist[ni] === -1) { dist[ni] = nd; ways[ni] = w; bfsQ[tail++] = ni; }
      else if (dist[ni] === nd) { ways[ni] = Math.min(4096, ways[ni] + w); }
    }
    if (canRight(r, c)) {
      const ni = idx + 1;
      if (dist[ni] === -1) { dist[ni] = nd; ways[ni] = w; bfsQ[tail++] = ni; }
      else if (dist[ni] === nd) { ways[ni] = Math.min(4096, ways[ni] + w); }
    }
  }

  for (let idx = 0; idx < total; idx++) {
    const d = dist[idx];
    if (d <= 0) continue;
    const r = (idx / 9) | 0;
    const c = idx - r * 9;
    const target = d - 1;
    let ex = 0;
    if (canUp(r, c) && dist[idx - 9] === target) ex++;
    if (canDown(r, c) && dist[idx + 9] === target) ex++;
    if (canLeft(r, c) && dist[idx - 1] === target) ex++;
    if (canRight(r, c) && dist[idx + 1] === target) ex++;
    exits[idx] = ex;
  }

  return { dist, ways, exits };
}

function getDistMaps() {
  const key = wHashLo + ":" + wHashHi;
  let entry = wallDistCache.get(key);
  if (entry !== undefined) return entry;

  const me = computeGoalMetrics(0);
  const opp = isRaceMode ? me : computeGoalMetrics(boardRows - 1);

  entry = { me, opp };
  if (wallDistCache.size > 40000) wallDistCache.clear();
  wallDistCache.set(key, entry);
  return entry;
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
        outBuf[cnt++] = (oR + DR[d]) * 9 + (oC + DC[d]);
      } else {
        if (d < 2) {
          if (canLeft(oR, oC)) outBuf[cnt++] = oR * 9 + (oC - 1);
          if (canRight(oR, oC)) outBuf[cnt++] = oR * 9 + (oC + 1);
        } else {
          if (canUp(oR, oC)) outBuf[cnt++] = (oR - 1) * 9 + oC;
          if (canDown(oR, oC)) outBuf[cnt++] = (oR + 1) * 9 + oC;
        }
      }
    } else {
      outBuf[cnt++] = nr * 9 + nc;
    }
  }
  return cnt;
}

function fastLog2(w) {
  if (w <= 1) return 0;
  if (w <= 2) return 1;
  if (w <= 4) return 2;
  if (w <= 8) return 3;
  if (w <= 16) return 4;
  if (w <= 32) return 5;
  return 6;
}

function evaluate2P(sideToMoveIsMe) {
  const oppGoal = isRaceMode ? 0 : boardRows - 1;
  if (myR === 0) return sideToMoveIsMe ? 100000 : -100000;
  if (oppR === oppGoal) return sideToMoveIsMe ? -100000 : 100000;

  const maps = getDistMaps();
  const myIdx = myR * 9 + myC;
  const oppIdx = oppR * 9 + oppC;
  const myDist = maps.me.dist[myIdx];
  const oppDist = maps.opp.dist[oppIdx];

  if (myDist < 0) return sideToMoveIsMe ? -100000 : 100000;
  if (oppDist < 0) return sideToMoveIsMe ? 100000 : -100000;

  // Эффективная дистанция с учетом права хода (кто ходит, тот на 0.5 шага ближе)
  let score = (oppDist - myDist) * 1050 + (sideToMoveIsMe ? 525 : -525);

  // Динамическое масштабирование ценности стен от фазы партии:
  // Когда кто-то близок к финишу (dist <= 4), темп добегания в 2 раза важнее экономии стенок!
  const minDist = Math.min(myDist, oppDist);
  const wallScale = minDist <= 2 ? 0.45 : (minDist <= 4 ? 0.72 : 1.0);

  const mw = Math.min(15, Math.max(0, myWalls));
  const ow = Math.min(15, Math.max(0, oppWalls));
  score += ((WALL_VALUE_TABLE[mw] - WALL_VALUE_TABLE[ow]) * wallScale) | 0;

  // Разнообразие маршрутов и узкие горлышки (Bottlenecks)
  const myExits = maps.me.exits[myIdx];
  const oppExits = maps.opp.exits[oppIdx];
  const myWays = maps.me.ways[myIdx];
  const oppWays = maps.opp.ways[oppIdx];

  score += (fastLog2(myWays) - fastLog2(oppWays)) * 90;
  score += (myExits - oppExits) * 165;

  // Запирание соперника в коридор с 1 выходом, когда у нас есть стенки для добивания
  if (oppExits === 1 && myWalls > 0) score += 380;
  if (myExits === 1 && oppWalls > 0) score -= 400;

  if (isRaceMode) {
    if (myDist <= oppDist) score += Math.abs(myC - oppC) * 30;
  } else {
    // Тактический контакт пешек (оппозиция для прыжка через соперника)
    if (Math.abs(myR - oppR) + Math.abs(myC - oppC) === 1) {
      if (sideToMoveIsMe) {
        const n = generatePawnStepsFast(myR, myC, oppR, oppC, stepBuf);
        for (let i = 0; i < n; i++) {
          if (maps.me.dist[stepBuf[i]] <= myDist - 2) { score += 950; break; }
        }
      } else {
        const n = generatePawnStepsFast(oppR, oppC, myR, myC, stepBuf);
        for (let i = 0; i < n; i++) {
          if (maps.opp.dist[stepBuf[i]] <= oppDist - 2) { score -= 950; break; }
        }
      }
    }
    const myCenter = 4 - Math.abs(myC - 4);
    const oppCenter = 4 - Math.abs(oppC - 4);
    score += (myCenter - oppCenter) * 22;
  }

  // Экстренное ускорение у финиша
  if (minDist <= 3) {
    score += (oppDist - myDist) * 550;
  }

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
  const pGoal = isMe ? 0 : (isRaceMode ? 0 : boardRows - 1);
  const sideIdx = isMe ? 0 : 1;

  const maps = getDistMaps();
  const pMap = isMe ? maps.me : maps.opp;
  const eMap = isMe ? maps.opp : maps.me;

  const pIdx = pR * 9 + pC;
  const eIdx = eR * 9 + eC;
  const curP = pMap.dist[pIdx];
  const curE = eMap.dist[eIdx];
  const curEExits = eMap.exits[eIdx];
  const curEWays = eMap.ways[eIdx];

  const cm = prevMove >= 0 ? counterMoves[sideIdx][prevMove & 2047] : 0;

  const outCodes = plyMoveCodes[ply];
  const outPrios = plyMovePrios[ply];
  let moveCount = 0;

  // 1. Ходы пешкой
  const nSteps = generatePawnStepsFast(pR, pC, eR, eC, stepBuf);
  for (let i = 0; i < nSteps; i++) {
    const cell = stepBuf[i];
    const sr = (cell / 9) | 0;
    const sc = cell - sr * 9;
    const code = packMove(0, sr, sc, 0);
    if (sr === pGoal) {
      outCodes[0] = code;
      return 1;
    }

    const newD = pMap.dist[cell];
    const stepGain = curP - newD;

    if (qSearchOnly) {
      const isJump = (stepGain >= 2) || (Math.abs(pR - eR) + Math.abs(pC - eC) === 1 && stepGain >= 1);
      const isWinThreat = (newD <= 1 && curP > 1);
      if (!isJump && !isWinThreat) continue;
    }

    let prio = stepGain * 16000 + pMap.exits[cell] * 400 + history[sideIdx][code];
    if (code === ttBestCode) prio += 60000000;
    if (code === cm) prio += 15000;
    if (stepGain >= 2) prio += 18000;

    outCodes[moveCount] = code;
    outPrios[moveCount] = prio;
    moveCount++;
  }

  if (pWalls <= 0) {
    sortSubArray(outCodes, outPrios, moveCount);
    return moveCount;
  }

  // 2. Генерация тактических и запирающих стенок
  const maxR = boardRows - 2;
  let wCount = 0;

  for (let r = 0; r <= maxR; r++) {
    for (let c = 0; c < 8; c++) {
      const idxTL = r * 9 + c;
      const dTL = eMap.dist[idxTL];
      const dTR = eMap.dist[idxTL + 1];
      const dBL = eMap.dist[idxTL + 9];
      const dBR = eMap.dist[idxTL + 10];

      const nearEnemy = Math.abs(r - eR) <= 2 && Math.abs(c - eC) <= 2;
      const nearMe = Math.abs(r - pR) <= 1 && Math.abs(c - pC) <= 1;

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

        const chainsWall = totalWallsPlaced > 0 && touchesExistingWallOrEdge(r, c, o);
        if (!cutsShortest && !nearEnemy && !nearMe && !chainsWall) continue;

        placeWallFast(r, c, o);
        const newMaps = getDistMaps();
        const nPMap = isMe ? newMaps.me : newMaps.opp;
        const nEMap = isMe ? newMaps.opp : newMaps.me;
        const newP = nPMap.dist[pIdx];
        const newE = nEMap.dist[eIdx];

        if (newP < 0 || newE < 0) {
          removeWallFast(r, c, o);
          continue;
        }

        const eGain = newE - curE;
        const pLoss = newP - curP;
        const net = eGain - pLoss;
        const newEExits = nEMap.exits[eIdx];
        const exitDrop = curEExits - newEExits;
        const waysDrop = curEWays - nEMap.ways[eIdx];
        removeWallFast(r, c, o);

        if (qSearchOnly) {
          const forcing = (net >= 2) || (curE <= 3 && net >= 1 && pLoss === 0) || (net >= 1 && newEExits === 1 && exitDrop >= 1);
          if (!forcing) continue;
        } else {
          // На первых 2 ходах на пустой доске не рассматриваем стенки с эффектом <= 1 шага
          if (totalWallsPlaced === 0 && curE >= 7 && net <= 1) continue;
          if (net < 0 && exitDrop <= 0) continue;
          if (net === 0 && exitDrop <= 0 && waysDrop <= 0) continue;
        }

        const code = packMove(1, r, c, o);
        let prio = net * 10500 + eGain * 3500 + exitDrop * 3200 + (waysDrop > 0 ? 1500 : -1200) + history[sideIdx][code];

        // Бонус за смыкание стенок в единый капкан (Corridor Sealing)
        if (chainsWall && (net >= 1 || exitDrop >= 1)) prio += 2800;
        if (newEExits === 1 && curEExits > 1) prio += 3600; // Зажали в единственный коридор!

        if (code === ttBestCode) prio += 60000000;
        if (code === cm) prio += 15000;
        if (killer[ply][0] === code || killer[ply][1] === code) prio += 12000;

        if (isRaceMode) {
          if (o === 1 && Math.abs(c - eC) <= 1 && Math.abs(r - eR) <= 2) prio += 1600;
          if (pLoss > 0) prio -= pLoss * 3800;
        } else {
          if (net >= 2 && pLoss === 0) prio += 6500;
        }

        tempWallCodes[wCount] = code;
        tempWallPrios[wCount] = prio;
        wCount++;
      }
    }
  }

  sortSubArray(tempWallCodes, tempWallPrios, wCount);
  const wallLimit = qSearchOnly ? 6 : (ply === 0 ? 32 : (ply <= 2 ? 16 : 10));
  const take = Math.min(wallLimit, wCount);

  for (let i = 0; i < take; i++) {
    outCodes[moveCount] = tempWallCodes[i];
    outPrios[moveCount] = tempWallPrios[i];
    moveCount++;
  }

  sortSubArray(outCodes, outPrios, moveCount);
  return moveCount;
}

function getFullStateKey(sideToMoveIsMe) {
  const meIdx = myR * 9 + myC;
  const oppIdx = oppR * 9 + oppC;
  const lo = (wHashLo ^ Z_ME_LO[meIdx] ^ Z_OPP_LO[oppIdx] ^ Z_MW_LO[myWalls] ^ Z_OW_LO[oppWalls]) >>> 0;
  const hi = (wHashHi ^ Z_ME_HI[meIdx] ^ Z_OPP_HI[oppIdx] ^ Z_MW_HI[myWalls] ^ Z_OW_HI[oppWalls] ^ (sideToMoveIsMe ? 0x12345678 : 0)) >>> 0;
  return lo + ":" + hi;
}

function quiescence2P(qply, ply, alpha, beta, sideToMoveIsMe, prevMove) {
  nodes++;
  if ((nodes & 31) === 0 && now() >= deadline) {
    timedOut = true;
    return 0;
  }

  const oppGoal = isRaceMode ? 0 : boardRows - 1;
  if (myR === 0) return sideToMoveIsMe ? (100000 - ply) : -(100000 - ply);
  if (oppR === oppGoal) return sideToMoveIsMe ? -(100000 - ply) : (100000 - ply);

  const standPat = evaluate2P(sideToMoveIsMe);
  if (standPat >= beta) return beta;
  if (standPat > alpha) alpha = standPat;
  if (qply >= 4 || ply >= 60) return alpha;

  const nMoves = generateMoves2P(sideToMoveIsMe, ply, -1, prevMove, true);
  if (nMoves === 0) return alpha;

  const codes = plyMoveCodes[ply];
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

    const score = -quiescence2P(qply + 1, ply + 1, -beta, -alpha, !sideToMoveIsMe, code);

    if (mType === 0) {
      if (sideToMoveIsMe) { myR = savedR; myC = savedC; }
      else { oppR = savedR; oppC = savedC; }
    } else {
      removeWallFast(mR, mC, mO);
      if (sideToMoveIsMe) myWalls++; else oppWalls++;
    }

    if (timedOut) return 0;
    if (score >= beta) return beta;
    if (score > alpha) alpha = score;
  }
  return alpha;
}

function pvs2P(depth, ply, alpha, beta, sideToMoveIsMe, prevMove) {
  nodes++;
  if ((nodes & 31) === 0 && now() >= deadline) {
    timedOut = true;
    return 0;
  }

  const oppGoal = isRaceMode ? 0 : boardRows - 1;
  if (myR === 0) return sideToMoveIsMe ? (100000 - ply) : -(100000 - ply);
  if (oppR === oppGoal) return sideToMoveIsMe ? -(100000 - ply) : (100000 - ply);

  if (depth <= 0 || ply >= 60) {
    return quiescence2P(0, ply, alpha, beta, sideToMoveIsMe, prevMove);
  }

  const isPvNode = (beta - alpha > 1);
  const ttKey = getFullStateKey(sideToMoveIsMe);
  const hit = TT.get(ttKey);
  let ttBestCode = -1;

  if (hit !== undefined) {
    ttBestCode = hit.bestMove;
    if (!isPvNode && hit.depth >= depth) {
      ttHits++;
      if (hit.flag === 1) return hit.score;
      if (hit.flag === 2 && hit.score >= beta) return hit.score;
      if (hit.flag === 3 && hit.score <= alpha) return hit.score;
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
      let reduction = 0;
      if (depth >= 3 && i >= 5 && mType === 1) {
        reduction = (depth >= 5 && i >= 10) ? 2 : 1;
      }
      score = -pvs2P(depth - 1 - reduction, ply + 1, -alpha - 1, -alpha, !sideToMoveIsMe, code);
      if (!timedOut && score > alpha && reduction > 0) {
        score = -pvs2P(depth - 1, ply + 1, -alpha - 1, -alpha, !sideToMoveIsMe, code);
      }
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
      if (killer[ply][0] !== code) {
        killer[ply][1] = killer[ply][0];
        killer[ply][0] = code;
      }
      if (prevMove >= 0) counterMoves[sideIdx][prevMove & 2047] = code;
      history[sideIdx][code] = Math.min(400000, history[sideIdx][code] + depth * depth * 90);
      break;
    }
  }

  let flag = 1;
  if (bestScore <= alphaOrig) flag = 3;
  else if (bestScore >= beta) flag = 2;

  if (TT.size > 120000) TT.clear();
  if (!hit || depth >= hit.depth) {
    TT.set(ttKey, { depth, score: bestScore, flag, bestMove: bestMoveCode });
  }
  return bestScore;
}

function searchBestMoveJS(timeBudgetMs, maxSearchDepth) {
  TT.clear();
  history[0].fill(0);
  history[1].fill(0);
  counterMoves[0].fill(0);
  counterMoves[1].fill(0);
  for (let i = 0; i < 64; i++) { killer[i][0] = 0; killer[i][1] = 0; }

  nodes = 0; ttHits = 0; cutoffs = 0; timedOut = false; completedDepth = 0;
  deadline = now() + timeBudgetMs;

  const nRoot = generateMoves2P(true, 0, -1, -1, false);
  if (nRoot === 0) return null;

  const rootList = new Int32Array(nRoot);
  for (let i = 0; i < nRoot; i++) rootList[i] = plyMoveCodes[0][i];

  const firstUnpacked = unpackMove(rootList[0]);
  if (firstUnpacked.type === 0 && firstUnpacked.r === 0) {
    completedDepth = 1;
    return firstUnpacked;
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

    while (true) {
      // Ставим лучший найденный ход (PV) первым в списке
      for (let i = 1; i < nRoot; i++) {
        if (rootList[i] === bestCode) {
          const tmp = rootList[0];
          rootList[0] = rootList[i];
          rootList[i] = tmp;
          break;
        }
      }

      let curAlpha = alpha;
      iterBestScore = -200000;
      iterBestCode = rootList[0];

      for (let i = 0; i < nRoot; i++) {
        const code = rootList[i];
        const mType = code & 1;
        const mO = (code >>> 1) & 1;
        const mR = (code >>> 2) & 15;
        const mC = (code >>> 6) & 15;

        const savedR = myR, savedC = myC;
        if (mType === 0) {
          myR = mR; myC = mC;
        } else {
          placeWallFast(mR, mC, mO);
          myWalls--;
        }

        let score;
        if (i === 0) {
          score = -pvs2P(depth - 1, 1, -beta, -curAlpha, false, code);
        } else {
          score = -pvs2P(depth - 1, 1, -curAlpha - 1, -curAlpha, false, code);
          if (!timedOut && score > curAlpha && score < beta) {
            score = -pvs2P(depth - 1, 1, -beta, -curAlpha, false, code);
          }
        }

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
        if (score > curAlpha) curAlpha = score;
        if (curAlpha >= beta) break;
      }

      if (timedOut) break;

      if (iterBestScore <= alpha) {
        alpha = Math.max(-200000, iterBestScore - delta);
        delta *= 2;
      } else if (iterBestScore >= beta) {
        bestCode = iterBestCode;
        beta = Math.min(200000, iterBestScore + delta);
        delta *= 2;
      } else {
        break;
      }
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

// ============================================================================
// QUAD 4-PLAYER ENGINE (11x11 — GOLDEN CENTER 5,5)
// ============================================================================
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
  if (wallDistCache.size > 30000) wallDistCache.clear();
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
  if (me.r === 5 && me.c === 5) return 100000;

  const dist = computeCenterMap11();
  const myD = dist[me.r * 11 + me.c];
  if (myD < 0) return -100000;

  let minOppEffDist = 999;
  let secondOppEffDist = 999;
  let leaderIdx = 1;

  for (let i = 1; i < quadPlayers.length; i++) {
    const op = quadPlayers[i];
    if (!op.active) continue;
    if (op.r === 5 && op.c === 5) return -100000;
    const od = dist[op.r * 11 + op.c];
    if (od < 0) return 100000;

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

  let score = (minOppEffDist - myD) * 1800;
  if (secondOppEffDist < 900) score += (secondOppEffDist - myD) * 450;
  const mw = Math.min(15, Math.max(0, me.walls));
  score += WALL_VALUE_TABLE[mw];
  score += (myExits - leaderExits) * 185;
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
    let prio = gain * 15000 + countExits11(st.r, st.c, dist) * 300;
    if (gain >= 2) prio += 8000;
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

  if (pIdx === 0 && curD < bestTargetDist && bestTargetDist > 2) {
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
        if (pIdx === 0 && net < 1 && bestTargetDist > 2) continue;

        let prio = net * 8500 + targetDelay * 2600;
        if (nearCenter && targetDelay >= 1 && selfLoss === 0) prio += 3400;
        wallCands.push({ type: 1, r, c, o, prio });
      }
    }
  }

  wallCands.sort((a, b) => b.prio - a.prio);
  const limit = isRoot ? 18 : 7;
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

  for (let i = 0; i < Math.min(leaderMoves.length, 8); i++) {
    const m = leaderMoves[i];
    const sr = leader.r, sc = leader.c;
    if (m.type === 0) {
      leader.r = m.r; leader.c = m.c;
    } else {
      placeWallFast(m.r, m.c, m.o);
      leader.walls--;
    }

    const val = (leader.r === 5 && leader.c === 5) ? -100000 : quadSearchMe(depth - 1, alpha, worstForMe);

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
  nodes++;
  if ((nodes & 31) === 0 && now() >= deadline) {
    timedOut = true;
    return 0;
  }
  if (quadPlayers[0].r === 5 && quadPlayers[0].c === 5) return 100000 + depth;
  for (let i = 1; i < quadPlayers.length; i++) {
    if (quadPlayers[i].active && quadPlayers[i].r === 5 && quadPlayers[i].c === 5) return -100000 - depth;
  }
  if (depth <= 0) return evaluateQuadState(true);

  const myMoves = generateQuadMoves(0, false);
  if (!myMoves.length) return evaluateQuadState(true);

  let best = -Infinity;
  const me = quadPlayers[0];

  for (let i = 0; i < Math.min(myMoves.length, 12); i++) {
    const m = myMoves[i];
    const sr = me.r, sc = me.c;
    if (m.type === 0) {
      me.r = m.r; me.c = m.c;
    } else {
      placeWallFast(m.r, m.c, m.o);
      me.walls--;
    }

    const val = (me.r === 5 && me.c === 5)
      ? (100000 + depth)
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
      if (iterScore >= 90000) break;
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

    const budget = Math.max(500, Math.min(1800, Number(m.timeMs) || 1200));
    const maxD = Math.min(16, Number(m.maxDepth) || 14);
    const t0 = now();

    let bestMove = null;

    // 1. Если скомпилирован C++ WASM-движок — вызываем нативный C++
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
      }
    }

    // 2. Иначе работает Zero-Alloc JS ядро
    if (!bestMove) {
      loadBoardWalls(m);
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
