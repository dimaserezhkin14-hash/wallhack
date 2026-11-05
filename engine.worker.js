"use strict";

// ============================================================================
// WALLHACK GRANDMASTER ENGINE WORKER (DUEL 9x9 + RACE 9x13)
// Zero-string allocation inside search, Zobrist TT, Goal-Distance Cache, PVS
// ============================================================================

let boardRows = 9;
let isRaceMode = false;
let deadline = 0;
let timedOut = false;
let nodes = 0;
let ttHits = 0;
let cutoffs = 0;
let completedDepth = 0;

// Плоские массивы стен (индекс: r * 8 + c, где r: 0..11, c: 0..7)
const hWalls = new Uint8Array(128);
const vWalls = new Uint8Array(128);

// Текущее состояние в поиске
let myR = 8, myC = 4, oppR = 0, oppC = 4;
let myWalls = 10, oppWalls = 10;
let totalWallsPlaced = 0;

// 64-битный Zobrist-хеш стенок (два 32-битных беззнаковых числа)
let wHashLo = 0, wHashHi = 0;

// Генерация таблиц Zobrist
const Z_HWALL_LO = new Uint32Array(128);
const Z_HWALL_HI = new Uint32Array(128);
const Z_VWALL_LO = new Uint32Array(128);
const Z_VWALL_HI = new Uint32Array(128);
const Z_ME_LO = new Uint32Array(128);
const Z_ME_HI = new Uint32Array(128);
const Z_OPP_LO = new Uint32Array(128);
const Z_OPP_HI = new Uint32Array(128);
const Z_MW_LO = new Uint32Array(20);
const Z_MW_HI = new Uint32Array(20);
const Z_OW_LO = new Uint32Array(20);
const Z_OW_HI = new Uint32Array(20);

(function initZobrist() {
  let seed = 0x9e3779b9;
  function rand32() {
    seed |= 0;
    seed = (seed + 0x6d2b79f5) | 0;
    let t = Math.imul(seed ^ (seed >>> 15), 1 | seed);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return (t ^ (t >>> 14)) >>> 0;
  }
  for (let i = 0; i < 128; i++) {
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

const TT = new Map();
const wallDistCache = new Map();
const killer = Array.from({ length: 32 }, () => [0, 0]);
const history = new Int32Array(1024);

const bfsQ = new Int16Array(160);

function now() {
  return typeof performance !== "undefined" ? performance.now() : Date.now();
}

// Быстрые проверки прохода между соседними клетками (без создания объектов и строк)
function canUp(r, c) {
  if (r <= 0) return false;
  const base = (r - 1) << 3;
  return (c >= 8 || hWalls[base + c] === 0) && (c <= 0 || hWalls[base + c - 1] === 0);
}
function canDown(r, c) {
  if (r >= boardRows - 1) return false;
  const base = r << 3;
  return (c >= 8 || hWalls[base + c] === 0) && (c <= 0 || hWalls[base + c - 1] === 0);
}
function canLeft(r, c) {
  if (c <= 0) return false;
  const col = c - 1;
  return (r >= boardRows - 1 || vWalls[(r << 3) + col] === 0) && (r <= 0 || vWalls[((r - 1) << 3) + col] === 0);
}
function canRight(r, c) {
  if (c >= 8) return false;
  return (r >= boardRows - 1 || vWalls[(r << 3) + c] === 0) && (r <= 0 || vWalls[((r - 1) << 3) + c] === 0);
}

function canStepDir(r, c, dir) {
  if (dir === 0) return canUp(r, c);
  if (dir === 1) return canDown(r, c);
  if (dir === 2) return canLeft(r, c);
  return canRight(r, c);
}

// Обратный мульти-BFS от целевого ряда: за 1 проход строит карту расстояний для ВСЕХ клеток доски
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

// Получение кэшированных карт расстояний для текущей конфигурации стен
function getDistMaps() {
  const key = wHashLo + ":" + wHashHi;
  let entry = wallDistCache.get(key);
  if (entry !== undefined) return entry;

  const meMap = computeGoalMap(0); // Мы всегда идем к r = 0
  // В гонке 9x13 противник тоже бежит к r = 0, поэтому карта идентична!
  const oppMap = isRaceMode ? meMap : computeGoalMap(boardRows - 1);

  entry = { meMap, oppMap };
  if (wallDistCache.size > 60000) wallDistCache.clear();
  wallDistCache.set(key, entry);
  return entry;
}

// Считает число оптимальных выходов (шагов, уменьшающих дистанцию) из клетки (r, c)
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

// Проверка геометрической легальности стены за O(1)
function wallGeometryLegal(r, c, o) {
  const maxR = boardRows - 2;
  if (r < 0 || r > maxR || c < 0 || c > 7) return false;
  const idx = (r << 3) + c;
  if (o === 0) { // Horizontal
    if (hWalls[idx] || vWalls[idx]) return false;
    if ((c > 0 && hWalls[idx - 1]) || (c < 7 && hWalls[idx + 1])) return false;
    return true;
  } else { // Vertical
    if (vWalls[idx] || hWalls[idx]) return false;
    if ((r > 0 && vWalls[idx - 8]) || (r < maxR && vWalls[idx + 8])) return false;
    return true;
  }
}

function placeWallFast(r, c, o) {
  const idx = (r << 3) + c;
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
  const idx = (r << 3) + c;
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

// Генерация легальных шагов пешки (включая прямые и диагональные прыжки)
const DR = [-1, 1, 0, 0];
const DC = [0, 0, -1, 1];

function getPawnSteps(pR, pC, oR, oC) {
  const out = [];
  for (let d = 0; d < 4; d++) {
    if (!canStepDir(pR, pC, d)) continue;
    const nr = pR + DR[d], nc = pC + DC[d];
    if (nr === oR && nc === oC) {
      // Прямой прыжок через фишку соперника
      if (canStepDir(oR, oC, d)) {
        out.push((oR + DR[d]) * 9 + (oC + DC[d]));
      } else {
        // Диагональные прыжки при преграде позади соперника
        if (d < 2) { // Шли вертикально -> пробуем влево/вправо от соперника
          if (canLeft(oR, oC)) out.push(oR * 9 + (oC - 1));
          if (canRight(oR, oC)) out.push(oR * 9 + (oC + 1));
        } else { // Шли горизонтально -> пробуем вверх/вниз от соперника
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

// ============================================================================
// СПЕЦИАЛИЗИРОВАННЫЕ АЛГОРИТМЫ ОЦЕНКИ: ДУЭЛЬ 9x9 vs ГОНКА 9x13
// ============================================================================
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

  // Учет права хода (темпа): тот, чей сейчас ход, фактически на 0.5 шага ближе
  const tempo = isMyTurn ? 750 : -750;
  const myExits = countOptimalExits(myR, myC, maps.meMap);
  const oppExits = countOptimalExits(oppR, oppC, maps.oppMap);

  if (isRaceMode) {
    // ------------------- АЛГОРИТМ 1: ГОНКА 9x13 -------------------
    let score = (oppDist - myDist) * 1650 + tempo;

    // Нелинейная ценность запаса стен (в гонке 15 стен)
    score += (myWalls - oppWalls) * 95;
    if (myWalls === 0 && oppWalls > 0) score -= 1400;
    if (oppWalls === 0 && myWalls > 0) score += 1400;

    // Свобода маневра (ширина коридора к финишу)
    score += (myExits - oppExits) * 140;
    if (oppExits <= 1 && myWalls > 0) score += 320; // Соперник зажат в узком туннеле
    if (myExits <= 1 && oppWalls > 0) score -= 340;

    // Сепарация дорожек: когда мы ведем в гонке, выгодно идти по отдельной колонке,
    // чтобы противник не мог одной стеной перекрыть нас и не задеть себя
    const colDiff = Math.abs(myC - oppC);
    if (myDist <= oppDist) {
      score += colDiff * 24;
    }

    // Давление в эндшпиле
    if (myDist <= 4 || oppDist <= 4) {
      score += (oppDist - myDist) * 550;
    }
    return score;
  } else {
    // ------------------- АЛГОРИТМ 2: ДУЭЛЬ 9x9 -------------------
    let score = (oppDist - myDist) * 1600 + tempo;

    // Учет контактного прыжка (если пешки стоят вплотную друг к другу)
    if (Math.abs(myR - oppR) + Math.abs(myC - oppC) === 1) {
      if (isMyTurn) {
        const steps = getPawnSteps(myR, myC, oppR, oppC);
        for (let i = 0; i < steps.length; i++) {
          if (maps.meMap[steps[i]] <= myDist - 2) { score += 900; break; }
        }
      } else {
        const steps = getPawnSteps(oppR, oppC, myR, myC);
        for (let i = 0; i < steps.length; i++) {
          if (maps.oppMap[steps[i]] <= oppDist - 2) { score -= 900; break; }
        }
      }
    }

    // Экономика стен в Дуэли 9x9: остаться с 0 стен против соперника со стенами смертельно
    score += (myWalls - oppWalls) * 85;
    if (myWalls === 0 && oppWalls > 0) score -= 1600;
    if (oppWalls === 0 && myWalls > 0) score += 1600;

    // Контроль альтернативных маршрутов (Exits)
    score += (myExits - oppExits) * 155;
    if (oppExits === 1 && myWalls > 0) score += 360;
    if (myExits === 1 && oppWalls > 0) score -= 380;

    // Контроль центра в дебюте и миттельшпиле
    const myCenter = 4 - Math.abs(myC - 4);
    const oppCenter = 4 - Math.abs(oppC - 4);
    score += (myCenter - oppCenter) * 18;

    // Обострение цены каждого темпа у финиша
    if (myDist <= 3 || oppDist <= 3) {
      score += (oppDist - myDist) * 600;
    }
    return score;
  }
}

// Кодирование хода в одно 32-битное число:
// type (0=step, 1=wall): bit 0
// o (0=h, 1=v): bit 1
// r (0..12): bits 2..5
// c (0..8): bits 6..9
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

// ============================================================================
// ГЕНЕРАЦИЯ И СОРТИРОВКА ХОДОВ (ШАГИ + УМНЫЙ ОТБОР СТЕН И 2-ХОДОВЫХ ЛОВУШЕК)
// ============================================================================
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

  // 1. Все легальные шаги пешкой
  const steps = getPawnSteps(pR, pC, eR, eC);
  for (let i = 0; i < steps.length; i++) {
    const cell = steps[i];
    const sr = (cell / 9) | 0;
    const sc = cell - sr * 9;
    const code = packMove(0, sr, sc, 0);

    // Победа в 1 ход — мгновенный возврат
    if (sr === pGoal) {
      return [code];
    }

    const newD = pMap[cell];
    const stepGain = curP - newD;
    let prio = stepGain * 10000 + history[code];

    if (code === ttBestCode) prio += 5000000;
    // На пустой доске в дебюте приоритет у быстрого захвата темпа пешкой
    if (totalWallsPlaced === 0 && stepGain > 0) prio += 7500;
    // Прыжок вперед через соперника (+2 клетки за 1 ход)
    if (stepGain >= 2) prio += 6000;

    moveCodes.push(code);
    movePrios.push(prio);
  }

  // Если стенок нет — сортируем только шаги
  if (pWalls <= 0) {
    return sortMoves(moveCodes, movePrios);
  }

  // 2. Генерация тактических стен (блокирующих, тормозящих и подготовительных L-ловушек)
  const maxR = boardRows - 2;
  const wallCodes = [];
  const wallPrios = [];

  for (let r = 0; r <= maxR; r++) {
    for (let c = 0; c < 8; c++) {
      // Быстрый фильтр релевантности: рассматриваем стены, которые находятся
      // рядом с пешкой врага, на градиенте его кратчайшего пути или рядом с уже стоящими стенами
      const idxTL = r * 9 + c;
      const dTL = eMap[idxTL];
      const dTR = eMap[idxTL + 1];
      const dBL = eMap[idxTL + 9];
      const dBR = eMap[idxTL + 10];

      const nearEnemy = Math.abs(r - eR) <= 3 && Math.abs(c - eC) <= 3;
      const nearMe = Math.abs(r - pR) <= 2 && Math.abs(c - pC) <= 2;

      for (let o = 0; o < 2; o++) {
        if (!wallGeometryLegal(r, c, o)) continue;

        // Проверяем, пересекает ли стена хотя бы одно ребро кратчайшего графа соперника
        let cutsGradient = false;
        if (o === 0) {
          cutsGradient = (Math.abs(dTL - dBL) === 1 && dTL <= curE) ||
                         (Math.abs(dTR - dBR) === 1 && dTR <= curE);
        } else {
          cutsGradient = (Math.abs(dTL - dTR) === 1 && dTL <= curE) ||
                         (Math.abs(dBL - dBR) === 1 && dBL <= curE);
        }

        if (!isRoot && !cutsGradient && !nearEnemy && !nearMe) continue;

        placeWallFast(r, c, o);
        const newMaps = getDistMaps();
        const nPMap = maximizing ? newMaps.meMap : newMaps.oppMap;
        const nEMap = maximizing ? newMaps.oppMap : newMaps.meMap;
        const newP = nPMap[pR * 9 + pC];
        const newE = nEMap[eR * 9 + eC];
        removeWallFast(r, c, o);

        // Запрещено полностью запирать любого игрока (newP === -1 или newE === -1)
        if (newP < 0 || newE < 0) continue;

        const eGain = newE - curE;
        const pLoss = newP - curP;
        const netDelta = eGain - pLoss;

        // Считаем, уменьшает ли стена число выходов соперника (подготовка 2-ходовой ловушки!)
        const newEExits = countOptimalExits(eR, eC, nEMap);
        const exitDrop = curEExits - newEExits;

        // Внутри дерева отсекаем бесполезные стены, которые не дают ни выигрыша темпа, ни сужения коридора
        if (!isRoot && netDelta < 0 && exitDrop <= 0) continue;
        if (!isRoot && netDelta === 0 && exitDrop <= 0 && !nearEnemy) continue;

        const code = packMove(1, r, c, o);
        let prio = netDelta * 6500 + eGain * 2200 + exitDrop * 1800 + history[code];

        if (code === ttBestCode) prio += 5000000;
        if (killer[depth][0] === code || killer[depth][1] === code) prio += 4500;

        // Дополнительные бонусы под конкретный режим
        if (isRaceMode) {
          // В гонке вертикальная стена между нами и соперником изолирует его дорожку
          if (o === 1 && Math.abs(c - eC) <= 1 && Math.abs(r - eR) <= 2) prio += 1100;
          // Жесткий штраф, если стена удлиняет наш собственный путь к финишу
          if (pLoss > 0) prio -= pLoss * 2400;
        } else {
          // В дуэли стена, которая разворачивает врага на 2+ хода при 0 потерь для нас — главный приоритет
          if (eGain >= 2 && pLoss === 0) prio += 4000;
        }

        // Не тратить стену на 1-м ходу партии без реального торможения соперника
        if (totalWallsPlaced === 0 && netDelta <= 0) prio -= 12000;

        wallCodes.push(code);
        wallPrios.push(prio);
      }
    }
  }

  const sortedWalls = sortMoves(wallCodes, wallPrios);
  const wallLimit = isRoot ? 42 : (depth >= 5 ? 12 : (depth >= 3 ? 16 : 20));
  const take = Math.min(wallLimit, sortedWalls.length);

  for (let i = 0; i < take; i++) {
    const wCode = sortedWalls[i];
    const idx = wallCodes.indexOf(wCode);
    moveCodes.push(wCode);
    movePrios.push(wallPrios[idx]);
  }

  return sortMoves(moveCodes, movePrios);
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

function getFullStateKey(maximizing) {
  const meIdx = myR * 9 + myC;
  const oppIdx = oppR * 9 + oppC;
  const lo = (wHashLo ^ Z_ME_LO[meIdx] ^ Z_OPP_LO[oppIdx] ^ Z_MW_LO[myWalls] ^ Z_OW_LO[oppWalls]) >>> 0;
  const hi = (wHashHi ^ Z_ME_HI[meIdx] ^ Z_OPP_HI[oppIdx] ^ Z_MW_HI[myWalls] ^ Z_OW_HI[oppWalls] ^ (maximizing ? 0x12345678 : 0)) >>> 0;
  return lo + ":" + hi;
}

// ============================================================================
// PRINCIPAL VARIATION SEARCH (PVS / ALPHA-BETA) С ТАБЛИЦЕЙ ТРАНСПОЗИЦИЙ
// ============================================================================
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

  const alpha0 = alpha, beta0 = beta;
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

    // Late Move Reduction (LMR) для поздних тихих ходов
    let nextDepth = depth - 1;
    if (depth >= 4 && i >= 8 && mType === 1) {
      nextDepth = depth - 2;
    }

    let val = pvs(nextDepth, !maximizing, alpha, beta);

    // Если редуцированный ход улучшает оценку — пересчитываем на полную глубину
    if (!timedOut && nextDepth < depth - 1) {
      if ((maximizing && val > alpha) || (!maximizing && val < beta)) {
        val = pvs(depth - 1, !maximizing, alpha, beta);
      }
    }

    // Откат хода
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
      history[code] = Math.min(200000, history[code] + depth * depth * 60);
      break;
    }
  }

  let flag = 0;
  if (bestScore <= alpha0) flag = 2;
  else if (bestScore >= beta0) flag = 1;

  if (TT.size > 150000) TT.clear();
  TT.set(ttKey, { depth, score: bestScore, flag, bestMove: bestMoveCode });
  return bestScore;
}

function searchBestMove(timeBudgetMs, maxSearchDepth) {
  TT.clear();
  history.fill(0);
  for (let i = 0; i < 32; i++) { killer[i][0] = 0; killer[i][1] = 0; }

  nodes = 0;
  ttHits = 0;
  cutoffs = 0;
  timedOut = false;
  completedDepth = 0;

  const start = now();
  deadline = start + timeBudgetMs;

  const rootMoves = generateMoves(true, 1, -1, true);
  if (rootMoves.length === 0) return null;

  // Если первый ход сразу приводит на линию финиша (r === 0) — играем мгновенно
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

    // Ставим лучший ход прошлой итерации (PV) первым для максимального отсечения
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
      if (iterBestScore >= 90000000) break; // Форсированная победа найдена
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
    return;
  }

  if (!m.walls) return;
  const addBank = (v, bank, o) => {
    const val = v >>> 0;
    for (let b = 0; b < 32; b++) {
      if ((val & (1 << b)) !== 0) {
        const idx = bank * 32 + b;
        placeWallFast((idx / 8) | 0, idx % 8, o);
      }
    }
  };
  addBank(m.walls.h0, 0, 0); addBank(m.walls.h1, 1, 0);
  addBank(m.walls.h2, 2, 0); addBank(m.walls.h3, 3, 0);
  addBank(m.walls.v0, 0, 1); addBank(m.walls.v1, 1, 1);
  addBank(m.walls.v2, 2, 1); addBank(m.walls.v3, 3, 1);
}

self.onmessage = function (e) {
  const m = e.data || {};
  try {
    if (m.type === "init") {
      self.postMessage({ type: "ready" });
      return;
    }
    if (m.type !== "search") return;

    const newRows = m.rows === 13 ? 13 : 9;
    if (newRows !== boardRows) {
      boardRows = newRows;
      isRaceMode = boardRows === 13;
      wallDistCache.clear();
    } else {
      isRaceMode = boardRows === 13;
    }

    myR = m.my.r; myC = m.my.c; myWalls = m.my.walls;
    oppR = m.opp.r; oppC = m.opp.c; oppWalls = m.opp.walls;

    loadBoardWalls(m);

    const budget = Math.max(400, Math.min(3000, Number(m.timeMs) || 1600));
    const maxD = Math.min(16, Number(m.maxDepth) || 14);

    const t0 = now();
    const bestMove = searchBestMove(budget, maxD);
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
