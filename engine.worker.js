"use strict";

// ============================================================================
// EXACT 1-TO-1 PORT OF NEMESIS (gorisanson/quoridor-ai v0.3 UCT MCTS)
// - Runs Native C++ WASM 60,000 Rollouts if engine.wasm is compiled
// - Otherwise runs Exact JS UCT MCTS (uctConst = 0.2, A = 0.7 rollout policy,
//   Robust Child selection by max visit count, 2-point connectivity filter)
// ============================================================================

let wasmSearchFn = null;
let wasmNodesFn = null;
let wasmDepthFn = null;
let wasmReady = false;
let engineType = "js-mcts";

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
      self.postMessage({ type: "ready", engine: "js-mcts" });
    });
  } else {
    self.postMessage({ type: "ready", engine: "js-mcts" });
  }
} catch (e) {
  self.postMessage({ type: "ready", engine: "js-mcts" });
}

function now() {
  return typeof performance !== "undefined" ? performance.now() : Date.now();
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

let boardRows = 9;
let boardCols = 9;
let isRaceMode = false;
let isQuadMode = false;

let rngState = 0x13579BDF;
function fastRand() {
  let x = rngState | 0;
  x ^= x << 13;
  x ^= x >>> 17;
  x ^= x << 5;
  rngState = x;
  return x >>> 0;
}
function fastRand01() {
  return (fastRand() & 0xFFFFFF) / 16777216.0;
}

const DR = [-1, 1, 0, 0];
const DC = [0, 0, -1, 1];
const bfsQ = new Int16Array(256);
const dMap0 = new Int8Array(169);
const dMap1 = new Int8Array(169);
const visBuf = new Uint8Array(169);

function goalRowOf(side) {
  if (isRaceMode) return 0;
  return side === 0 ? 0 : (boardRows - 1);
}

function canUpB(hWalls, r, c) {
  if (r <= 0) return false;
  const wC = boardCols - 1;
  const base = (r - 1) * wC;
  return (c >= wC || hWalls[base + c] === 0) && (c <= 0 || hWalls[base + c - 1] === 0);
}
function canDownB(hWalls, r, c) {
  if (r >= boardRows - 1) return false;
  const wC = boardCols - 1;
  const base = r * wC;
  return (c >= wC || hWalls[base + c] === 0) && (c <= 0 || hWalls[base + c - 1] === 0);
}
function canLeftB(vWalls, r, c) {
  if (c <= 0) return false;
  const wC = boardCols - 1;
  return (r >= boardRows - 1 || vWalls[r * wC + c - 1] === 0) && (r <= 0 || vWalls[(r - 1) * wC + c - 1] === 0);
}
function canRightB(vWalls, r, c) {
  const wC = boardCols - 1;
  if (c >= wC) return false;
  return (r >= boardRows - 1 || vWalls[r * wC + c] === 0) && (r <= 0 || vWalls[(r - 1) * wC + c] === 0);
}
function canStepDirB(hWalls, vWalls, r, c, d) {
  if (d === 0) return canUpB(hWalls, r, c);
  if (d === 1) return canDownB(hWalls, r, c);
  if (d === 2) return canLeftB(vWalls, r, c);
  return canRightB(vWalls, r, c);
}

function wallGeometryLegalB(hWalls, vWalls, r, c, o) {
  const maxR = boardRows - 2, maxC = boardCols - 2;
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

// Exact testIfConnectedOnTwoPoints from gorisanson/quoridor-ai game.js
function isConnectedOnTwoPointsB(hWalls, vWalls, r, c, o) {
  const stride = boardCols - 1;
  const maxR = boardRows - 2, maxC = boardCols - 2;
  if (o === 0) {
    let left = (c === 0);
    if (!left && c >= 1) {
      if (vWalls[r * stride + (c - 1)] ||
          (r >= 1 && vWalls[(r - 1) * stride + (c - 1)]) ||
          (r < maxR && vWalls[(r + 1) * stride + (c - 1)]) ||
          (c >= 2 && hWalls[r * stride + (c - 2)])) left = true;
    }
    let right = (c === maxC);
    if (!right && c < maxC) {
      if (vWalls[r * stride + (c + 1)] ||
          (r >= 1 && vWalls[(r - 1) * stride + (c + 1)]) ||
          (r < maxR && vWalls[(r + 1) * stride + (c + 1)]) ||
          (c + 2 <= maxC && hWalls[r * stride + (c + 2)])) right = true;
    }
    const middle = (r >= 1 && vWalls[(r - 1) * stride + c]) || (r < maxR && vWalls[(r + 1) * stride + c]);
    return (left && right) || (right && middle) || (middle && left);
  } else {
    let top = (r === 0);
    if (!top && r >= 1) {
      if (hWalls[(r - 1) * stride + c] ||
          (c >= 1 && hWalls[(r - 1) * stride + (c - 1)]) ||
          (c < maxC && hWalls[(r - 1) * stride + (c + 1)]) ||
          (r >= 2 && vWalls[(r - 2) * stride + c])) top = true;
    }
    let bottom = (r === maxR);
    if (!bottom && r < maxR) {
      if (hWalls[(r + 1) * stride + c] ||
          (c >= 1 && hWalls[(r + 1) * stride + (c - 1)]) ||
          (c < maxC && hWalls[(r + 1) * stride + (c + 1)]) ||
          (r + 2 <= maxR && vWalls[(r + 2) * stride + c])) bottom = true;
    }
    const middle = (c >= 1 && hWalls[r * stride + (c - 1)]) || (c < maxC && hWalls[r * stride + (c + 1)]);
    return (top && bottom) || (bottom && middle) || (middle && top);
  }
}

function computeDistToGoal(hWalls, vWalls, goalRow, outDist) {
  const total = boardRows * boardCols;
  outDist.fill(-1, 0, total);
  let head = 0, tail = 0;
  const base = goalRow * boardCols;
  for (let c = 0; c < boardCols; c++) {
    outDist[base + c] = 0;
    bfsQ[tail++] = base + c;
  }
  while (head < tail) {
    const idx = bfsQ[head++];
    const r = (idx / boardCols) | 0;
    const c = idx - r * boardCols;
    const nd = outDist[idx] + 1;
    if (canUpB(hWalls, r, c) && outDist[idx - boardCols] === -1) { outDist[idx - boardCols] = nd; bfsQ[tail++] = idx - boardCols; }
    if (canDownB(hWalls, r, c) && outDist[idx + boardCols] === -1) { outDist[idx + boardCols] = nd; bfsQ[tail++] = idx + boardCols; }
    if (canLeftB(vWalls, r, c) && outDist[idx - 1] === -1) { outDist[idx - 1] = nd; bfsQ[tail++] = idx - 1; }
    if (canRightB(vWalls, r, c) && outDist[idx + 1] === -1) { outDist[idx + 1] = nd; bfsQ[tail++] = idx + 1; }
  }
}

function hasPathToGoal(hWalls, vWalls, startR, startC, goalRow) {
  const total = boardRows * boardCols;
  visBuf.fill(0, 0, total);
  let head = 0, tail = 0;
  const startIdx = startR * boardCols + startC;
  visBuf[startIdx] = 1;
  bfsQ[tail++] = startIdx;
  while (head < tail) {
    const idx = bfsQ[head++];
    const r = (idx / boardCols) | 0;
    if (r === goalRow) return true;
    const c = idx - r * boardCols;
    if (canUpB(hWalls, r, c) && !visBuf[idx - boardCols]) { visBuf[idx - boardCols] = 1; bfsQ[tail++] = idx - boardCols; }
    if (canDownB(hWalls, r, c) && !visBuf[idx + boardCols]) { visBuf[idx + boardCols] = 1; bfsQ[tail++] = idx + boardCols; }
    if (canLeftB(vWalls, r, c) && !visBuf[idx - 1]) { visBuf[idx - 1] = 1; bfsQ[tail++] = idx - 1; }
    if (canRightB(vWalls, r, c) && !visBuf[idx + 1]) { visBuf[idx + 1] = 1; bfsQ[tail++] = idx + 1; }
  }
  return false;
}

function isWallLegalFull(st, r, c, o) {
  if (!wallGeometryLegalB(st.hWalls, st.vWalls, r, c, o)) return false;
  if (!isConnectedOnTwoPointsB(st.hWalls, st.vWalls, r, c, o)) return true;
  const idx = r * (boardCols - 1) + c;
  if (o === 0) st.hWalls[idx] = 1; else st.vWalls[idx] = 1;
  const ok = hasPathToGoal(st.hWalls, st.vWalls, st.pR0, st.pC0, goalRowOf(0)) &&
             hasPathToGoal(st.hWalls, st.vWalls, st.pR1, st.pC1, goalRowOf(1));
  if (o === 0) st.hWalls[idx] = 0; else st.vWalls[idx] = 0;
  return ok;
}

function isProbableWallNemesis(st, r, c, o) {
  const maxR = boardRows - 2, maxC = boardCols - 2;
  const stride = boardCols - 1;

  if (o === 0) {
    if ((r === st.pR0 - 1 || r === st.pR0) && c >= st.pC0 - 2 && c <= st.pC0 + 1) return true;
    if ((r === st.pR1 - 1 || r === st.pR1) && c >= st.pC1 - 2 && c <= st.pC1 + 1) return true;
    if (st.totalWalls >= 2 && (c === 0 || c === maxC)) return true;
  } else {
    if ((c === st.pC0 - 1 || c === st.pC0) && r >= st.pR0 - 2 && r <= st.pR0 + 1) return true;
    if ((c === st.pC1 - 1 || c === st.pC1) && r >= st.pR1 - 2 && r <= st.pR1 + 1) return true;
  }

  if (st.totalWalls > 0) {
    if (o === 0) {
      if (c >= 2 && st.hWalls[r * stride + (c - 2)]) return true;
      if (c + 2 <= maxC && st.hWalls[r * stride + (c + 2)]) return true;
      if (c >= 3 && st.hWalls[r * stride + (c - 3)]) return true;
      if (c + 3 <= maxC && st.hWalls[r * stride + (c + 3)]) return true;
      for (let dr = -2; dr <= 2; dr++) {
        const nr = r + dr;
        if (nr < 0 || nr > maxR) continue;
        for (let dc = -1; dc <= 1; dc++) {
          const nc = c + dc;
          if (nc >= 0 && nc <= maxC && st.vWalls[nr * stride + nc]) return true;
        }
      }
    } else {
      if (r >= 2 && st.vWalls[(r - 2) * stride + c]) return true;
      if (r + 2 <= maxR && st.vWalls[(r + 2) * stride + c]) return true;
      if (r >= 3 && st.vWalls[(r - 3) * stride + c]) return true;
      if (r + 3 <= maxR && st.vWalls[(r + 3) * stride + c]) return true;
      for (let dr = -1; dr <= 1; dr++) {
        const nr = r + dr;
        if (nr < 0 || nr > maxR) continue;
        for (let dc = -2; dc <= 2; dc++) {
          const nc = c + dc;
          if (nc >= 0 && nc <= maxC && st.hWalls[nr * stride + nc]) return true;
        }
      }
    }
  }
  return false;
}

const stepOutBuf = new Int32Array(12);
function generatePawnStepsB(st, side) {
  const pR = side === 0 ? st.pR0 : st.pR1;
  const pC = side === 0 ? st.pC0 : st.pC1;
  const oR = side === 0 ? st.pR1 : st.pR0;
  const oC = side === 0 ? st.pC1 : st.pC0;
  let cnt = 0;
  for (let d = 0; d < 4; d++) {
    if (!canStepDirB(st.hWalls, st.vWalls, pR, pC, d)) continue;
    const nr = pR + DR[d], nc = pC + DC[d];
    if (nr === oR && nc === oC) {
      if (canStepDirB(st.hWalls, st.vWalls, oR, oC, d)) {
        stepOutBuf[cnt++] = (oR + DR[d]) * boardCols + (oC + DC[d]);
      } else {
        if (d < 2) {
          if (canLeftB(st.vWalls, oR, oC)) stepOutBuf[cnt++] = oR * boardCols + (oC - 1);
          if (canRightB(st.vWalls, oR, oC)) stepOutBuf[cnt++] = oR * boardCols + (oC + 1);
        } else {
          if (canUpB(st.hWalls, oR, oC)) stepOutBuf[cnt++] = (oR - 1) * boardCols + oC;
          if (canDownB(st.hWalls, oR, oC)) stepOutBuf[cnt++] = (oR + 1) * boardCols + oC;
        }
      }
    } else {
      stepOutBuf[cnt++] = nr * boardCols + nc;
    }
  }
  return cnt;
}

function cloneState(st) {
  return {
    hWalls: new Uint8Array(st.hWalls),
    vWalls: new Uint8Array(st.vWalls),
    pR0: st.pR0, pC0: st.pC0, pW0: st.pW0,
    pR1: st.pR1, pC1: st.pC1, pW1: st.pW1,
    turn: st.turn,
    totalWalls: st.totalWalls
  };
}

function applyMoveState(st, code) {
  const mType = code & 1;
  const mO = (code >>> 1) & 1;
  const mR = (code >>> 2) & 15;
  const mC = (code >>> 6) & 15;
  if (mType === 0) {
    if (st.turn === 0) { st.pR0 = mR; st.pC0 = mC; }
    else { st.pR1 = mR; st.pC1 = mC; }
  } else {
    const idx = mR * (boardCols - 1) + mC;
    if (mO === 0) st.hWalls[idx] = 1; else st.vWalls[idx] = 1;
    if (st.turn === 0) st.pW0--; else st.pW1--;
    st.totalWalls++;
  }
  st.turn = 1 - st.turn;
}

function getExpansionMoves(st) {
  const s = st.turn;
  const opp = 1 - s;
  const gMy = goalRowOf(s);
  const gOpp = goalRowOf(opp);

  computeDistToGoal(st.hWalls, st.vWalls, gMy, dMap0);
  computeDistToGoal(st.hWalls, st.vWalls, gOpp, dMap1);

  const myR = s === 0 ? st.pR0 : st.pR1, myC = s === 0 ? st.pC0 : st.pC1;
  const oppR = s === 0 ? st.pR1 : st.pR0, oppC = s === 0 ? st.pC1 : st.pC0;
  const myW = s === 0 ? st.pW0 : st.pW1, oppW = s === 0 ? st.pW1 : st.pW0;

  const curMyD = dMap0[myR * boardCols + myC];
  const curOppD = dMap1[oppR * boardCols + oppC];

  const moves = [];
  const nSteps = generatePawnStepsB(st, s);
  let bestStepD = 999;
  for (let i = 0; i < nSteps; i++) {
    const cell = stepOutBuf[i];
    const sr = (cell / boardCols) | 0;
    if (sr === gMy) return [packMove(0, sr, cell % boardCols, 0)];
    if (dMap0[cell] >= 0 && dMap0[cell] < bestStepD) bestStepD = dMap0[cell];
  }

  for (let i = 0; i < nSteps; i++) {
    const cell = stepOutBuf[i];
    if (oppW === 0 && dMap0[cell] > bestStepD) continue;
    moves.push(packMove(0, (cell / boardCols) | 0, cell % boardCols, 0));
  }

  if (myW <= 0) return moves;
  if (oppW === 0 && curMyD <= curOppD) return moves;

  const maxR = boardRows - 2, maxC = boardCols - 2;
  for (let r = 0; r <= maxR; r++) {
    for (let c = 0; c <= maxC; c++) {
      const idxTL = r * boardCols + c;
      const dTL = dMap1[idxTL], dTR = dMap1[idxTL + 1];
      const dBL = dMap1[idxTL + boardCols], dBR = dMap1[idxTL + boardCols + 1];

      for (let o = 0; o < 2; o++) {
        if (!wallGeometryLegalB(st.hWalls, st.vWalls, r, c, o)) continue;
        let disturbsOpp = false;
        if (o === 0) {
          disturbsOpp = (Math.abs(dTL - dBL) === 1 && Math.min(dTL, dBL) < curOppD) ||
                        (Math.abs(dTR - dBR) === 1 && Math.min(dTR, dBR) < curOppD);
        } else {
          disturbsOpp = (Math.abs(dTL - dTR) === 1 && Math.min(dTL, dTR) < curOppD) ||
                        (Math.abs(dBL - dBR) === 1 && Math.min(dBL, dBR) < curOppD);
        }
        if (oppW === 0) {
          if (!disturbsOpp) continue;
        } else {
          if (!disturbsOpp && !isProbableWallNemesis(st, r, c, o)) continue;
        }
        if (!isWallLegalFull(st, r, c, o)) continue;
        moves.push(packMove(1, r, c, o));
      }
    }
  }
  return moves;
}

const wallRolloutBuf = new Int32Array(128);

function simulateRolloutJS(st) {
  for (let step = 0; step < 110; step++) {
    if (st.pR0 === goalRowOf(0)) return 0;
    if (st.pR1 === goalRowOf(1)) return 1;

    if (st.pW0 === 0 && st.pW1 === 0) {
      computeDistToGoal(st.hWalls, st.vWalls, goalRowOf(0), dMap0);
      computeDistToGoal(st.hWalls, st.vWalls, goalRowOf(1), dMap1);
      const dist0 = dMap0[st.pR0 * boardCols + st.pC0];
      const dist1 = dMap1[st.pR1 * boardCols + st.pC1];
      return st.turn === 0 ? (dist0 <= dist1 ? 0 : 1) : (dist1 <= dist0 ? 1 : 0);
    }

    const s = st.turn;
    const gMy = goalRowOf(s);
    const myW = s === 0 ? st.pW0 : st.pW1;

    if (fastRand01() < 0.70) {
      computeDistToGoal(st.hWalls, st.vWalls, gMy, dMap0);
      const nSteps = generatePawnStepsB(st, s);
      let bestD = 999, bestCell = stepOutBuf[0], nBest = 0;
      for (let i = 0; i < nSteps; i++) {
        const cell = stepOutBuf[i];
        const d = dMap0[cell];
        if (d >= 0 && d < bestD) { bestD = d; bestCell = cell; nBest = 1; }
        else if (d === bestD && (fastRand() & 1)) { bestCell = cell; nBest++; }
      }
      if (s === 0) { st.pR0 = (bestCell / boardCols) | 0; st.pC0 = bestCell % boardCols; }
      else { st.pR1 = (bestCell / boardCols) | 0; st.pC1 = bestCell % boardCols; }
      st.turn = 1 - s;
      continue;
    }

    if (myW > 0) {
      let nW = 0;
      const maxR = boardRows - 2, maxC = boardCols - 2;
      for (let r = 0; r <= maxR; r++) {
        for (let c = 0; c <= maxC; c++) {
          for (let o = 0; o < 2; o++) {
            if (wallGeometryLegalB(st.hWalls, st.vWalls, r, c, o) && isProbableWallNemesis(st, r, c, o)) {
              wallRolloutBuf[nW++] = packMove(1, r, c, o);
            }
          }
        }
      }
      let placed = false;
      for (let tries = 0; tries < 5 && nW > 0; tries++) {
        const idx = fastRand() % nW;
        const code = wallRolloutBuf[idx];
        const wm = unpackMove(code);
        if (isWallLegalFull(st, wm.r, wm.c, wm.o)) {
          applyMoveState(st, code);
          placed = true;
          break;
        }
        wallRolloutBuf[idx] = wallRolloutBuf[--nW];
      }
      if (placed) continue;
    } else {
      // 0 walls left penalty: move backwards
      computeDistToGoal(st.hWalls, st.vWalls, gMy, dMap0);
      const nSteps = generatePawnStepsB(st, s);
      let worstD = -1, worstCell = stepOutBuf[0];
      for (let i = 0; i < nSteps; i++) {
        const cell = stepOutBuf[i];
        if (dMap0[cell] > worstD) { worstD = dMap0[cell]; worstCell = cell; }
      }
      if (s === 0) { st.pR0 = (worstCell / boardCols) | 0; st.pC0 = worstCell % boardCols; }
      else { st.pR1 = (worstCell / boardCols) | 0; st.pC1 = worstCell % boardCols; }
      st.turn = 1 - s;
      continue;
    }

    computeDistToGoal(st.hWalls, st.vWalls, gMy, dMap0);
    const nSteps = generatePawnStepsB(st, s);
    let bestD = 999, bestCell = stepOutBuf[0];
    for (let i = 0; i < nSteps; i++) {
      const cell = stepOutBuf[i];
      if (dMap0[cell] >= 0 && dMap0[cell] < bestD) { bestD = dMap0[cell]; bestCell = cell; }
    }
    if (s === 0) { st.pR0 = (bestCell / boardCols) | 0; st.pC0 = bestCell % boardCols; }
    else { st.pR1 = (bestCell / boardCols) | 0; st.pC1 = bestCell % boardCols; }
    st.turn = 1 - s;
  }

  computeDistToGoal(st.hWalls, st.vWalls, goalRowOf(0), dMap0);
  computeDistToGoal(st.hWalls, st.vWalls, goalRowOf(1), dMap1);
  return dMap0[st.pR0 * boardCols + st.pC0] <= dMap1[st.pR1 * boardCols + st.pC1] ? 0 : 1;
}

function searchNemesisMCTS_JS(rootSt, budgetMs) {
  const nSteps = generatePawnStepsB(rootSt, 0);
  for (let i = 0; i < nSteps; i++) {
    const r = (stepOutBuf[i] / boardCols) | 0, c = stepOutBuf[i] % boardCols;
    if (r === goalRowOf(0)) return { move: { type: 0, r, c, o: 0 }, sims: 1, depth: 1 };
  }

  if (rootSt.pW0 === 0 && rootSt.pW1 === 0) {
    computeDistToGoal(rootSt.hWalls, rootSt.vWalls, goalRowOf(0), dMap0);
    let bestD = 999, bestCell = stepOutBuf[0];
    for (let i = 0; i < nSteps; i++) {
      const cell = stepOutBuf[i];
      if (dMap0[cell] >= 0 && dMap0[cell] < bestD) { bestD = dMap0[cell]; bestCell = cell; }
    }
    return { move: { type: 0, r: (bestCell / boardCols) | 0, c: bestCell % boardCols, o: 0 }, sims: 1, depth: 20 };
  }

  const rootNode = {
    parent: null,
    moveCode: 0,
    moverSide: 1,
    visits: 0,
    wins: 0,
    children: null,
    untriedMoves: getExpansionMoves(rootSt)
  };

  if (rootNode.untriedMoves.length === 1) {
    return { move: unpackMove(rootNode.untriedMoves[0]), sims: 1, depth: 1 };
  }

  const deadline = now() + budgetMs;
  const UCT_CONST = 0.2;
  let sims = 0;
  let maxDepth = 1;

  for (; sims < 60000; sims++) {
    if ((sims & 63) === 0 && now() >= deadline) break;

    const simSt = cloneState(rootSt);
    let node = rootNode;
    let depth = 0;

    // Selection
    while (node.untriedMoves.length === 0 && node.children && node.children.length > 0) {
      let bestChild = node.children[0];
      let bestUCT = -1e18;
      const logP = Math.log(Math.max(1, node.visits));
      for (let i = 0; i < node.children.length; i++) {
        const ch = node.children[i];
        const uct = (ch.wins / ch.visits) + UCT_CONST * Math.sqrt(logP / ch.visits);
        if (uct > bestUCT) { bestUCT = uct; bestChild = ch; }
      }
      node = bestChild;
      applyMoveState(simSt, node.moveCode);
      depth++;
    }

    // Expansion
    if (node.untriedMoves.length > 0) {
      const idx = fastRand() % node.untriedMoves.length;
      const code = node.untriedMoves[idx];
      node.untriedMoves[idx] = node.untriedMoves[node.untriedMoves.length - 1];
      node.untriedMoves.pop();

      const mover = simSt.turn;
      applyMoveState(simSt, code);
      depth++;

      const child = {
        parent: node,
        moveCode: code,
        moverSide: mover,
        visits: 0,
        wins: 0,
        children: null,
        untriedMoves: (simSt.pR0 === goalRowOf(0) || simSt.pR1 === goalRowOf(1)) ? [] : getExpansionMoves(simSt)
      };
      if (!node.children) node.children = [];
      node.children.push(child);
      node = child;
    }

    if (depth > maxDepth) maxDepth = depth;

    // Simulation
    const winner = simulateRolloutJS(simSt);

    // Backpropagation
    while (node !== null) {
      node.visits++;
      if (node.moverSide === winner) node.wins += 1.0;
      node = node.parent;
    }
  }

  // Robust child selection (highest visit count)
  let bestChild = rootNode.children[0];
  for (let i = 1; i < rootNode.children.length; i++) {
    const ch = rootNode.children[i];
    if (ch.visits > bestChild.visits ||
       (ch.visits === bestChild.visits && (ch.wins / ch.visits) > (bestChild.wins / bestChild.visits))) {
      bestChild = ch;
    }
  }

  return {
    move: unpackMove(bestChild.moveCode),
    sims,
    depth: maxDepth
  };
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

    const budget = Math.max(800, Math.min(3500, Number(m.timeMs) || 2000));
    const maxD = Math.min(20, Number(m.maxDepth) || 16);
    const t0 = now();

    let bestMove = null;
    let nodes = 0;
    let completedDepth = 0;
    let usedEngine = "js-mcts";

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
      const rootSt = {
        hWalls: new Uint8Array(169),
        vWalls: new Uint8Array(169),
        pR0: m.my.r, pC0: m.my.c, pW0: m.my.walls,
        pR1: m.opp.r, pC1: m.opp.c, pW1: m.opp.walls,
        turn: 0,
        totalWalls: 0
      };
      if (Array.isArray(m.wallList)) {
        for (let i = 0; i < m.wallList.length; i++) {
          const parts = String(m.wallList[i]).split(",");
          const r = +parts[0], c = +parts[1], o = parts[2] === "h" ? 0 : 1;
          const idx = r * (boardCols - 1) + c;
          if (o === 0) rootSt.hWalls[idx] = 1; else rootSt.vWalls[idx] = 1;
          rootSt.totalWalls++;
        }
      }
      const res = searchNemesisMCTS_JS(rootSt, budget);
      bestMove = res.move;
      nodes = res.sims;
      completedDepth = res.depth;
      usedEngine = "js-mcts";
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
      ttHits: 0,
      cutoffs: 0
    });
  } catch (err) {
    self.postMessage({
      type: "error",
      id: m.id,
      message: String((err && err.stack) || err)
    });
  }
};
