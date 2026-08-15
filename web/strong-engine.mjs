import {
  Outcome,
  Player,
  applyMove,
  evaluateState,
  legalMoves,
  outcomeBeforeMobility,
  positionKey,
  terminalOutcome,
} from "./engine.mjs";

class SearchTimeout extends Error {}

function terminalValue(outcome, rootPlayer, remainingDepth) {
  if (outcome === Outcome.DRAW) return 0;
  const winner = outcome === Outcome.BLUE_WIN ? Player.BLUE : Player.RED;
  const magnitude = 1_000_000 + remainingDepth;
  return winner === rootPlayer ? magnitude : -magnitude;
}

function orderedChildren(state, moves, rootPlayer, maximizing) {
  const children = moves.map((move) => {
    const child = applyMove(state, move, { validate: false });
    const outcome = outcomeBeforeMobility(child);
    const orderScore = outcome === Outcome.ONGOING
      ? evaluateState(child, rootPlayer)
      : terminalValue(outcome, rootPlayer, 0);
    return { move, child, orderScore };
  });
  children.sort((a, b) => maximizing
    ? b.orderScore - a.orderScore
    : a.orderScore - b.orderScore);
  return children;
}

function searchNode(state, depth, alpha, beta, rootPlayer, deadline, path, tt, counter) {
  counter.nodes += 1;
  if ((counter.nodes & 127) === 0 && performance.now() >= deadline) {
    throw new SearchTimeout();
  }

  const outcome = terminalOutcome(state);
  if (outcome !== Outcome.ONGOING) return terminalValue(outcome, rootPlayer, depth);
  if (depth === 0) return evaluateState(state, rootPlayer);

  const baseKey = positionKey(state);
  if (path.has(baseKey)) return 0;

  const maximizing = state.nextPlayer === rootPlayer;
  const ttKey = `${baseKey}|${rootPlayer}`;
  const cached = tt.get(ttKey);
  const originalAlpha = alpha;
  const originalBeta = beta;
  if (cached && cached.depth >= depth) {
    counter.ttHits += 1;
    if (cached.flag === "exact") return cached.score;
    if (cached.flag === "lower") alpha = Math.max(alpha, cached.score);
    if (cached.flag === "upper") beta = Math.min(beta, cached.score);
    if (alpha >= beta) return cached.score;
  }

  path.add(baseKey);
  let best = maximizing ? -Infinity : Infinity;
  try {
    const children = orderedChildren(state, legalMoves(state), rootPlayer, maximizing);
    for (const { child } of children) {
      const score = searchNode(
        child,
        depth - 1,
        alpha,
        beta,
        rootPlayer,
        deadline,
        path,
        tt,
        counter,
      );
      if (maximizing) {
        best = Math.max(best, score);
        alpha = Math.max(alpha, best);
      } else {
        best = Math.min(best, score);
        beta = Math.min(beta, best);
      }
      if (beta <= alpha) {
        counter.cutoffs += 1;
        break;
      }
    }
  } finally {
    path.delete(baseKey);
  }

  let flag = "exact";
  if (best <= originalAlpha) flag = "upper";
  else if (best >= originalBeta) flag = "lower";
  tt.set(ttKey, { depth, score: best, flag });
  return best;
}

function immediateWinningMove(state, moves, player) {
  for (const move of moves) {
    const child = applyMove(state, move, { validate: false });
    const outcome = outcomeBeforeMobility(child);
    if (
      (player === Player.BLUE && outcome === Outcome.BLUE_WIN) ||
      (player === Player.RED && outcome === Outcome.RED_WIN)
    ) return move;
  }
  return null;
}

export function chooseComputerMove(
  state,
  { difficulty = "medium", timeLimitMs = 700, maxDepth = null, random = Math.random } = {},
) {
  const moves = legalMoves(state);
  if (moves.length === 0) return null;

  const rootPlayer = state.nextPlayer;
  const winning = immediateWinningMove(state, moves, rootPlayer);
  if (winning) {
    return {
      move: winning,
      score: 1_000_000,
      depth: 1,
      nodes: moves.length,
      ttHits: 0,
      cutoffs: 0,
      timedOut: false,
    };
  }

  if (difficulty === "easy") {
    const index = Math.floor(random() * moves.length);
    return {
      move: moves[index],
      score: 0,
      depth: 0,
      nodes: 0,
      ttHits: 0,
      cutoffs: 0,
      timedOut: false,
    };
  }

  const depthCap = maxDepth ?? (
    difficulty === "strong" ? 64 : difficulty === "hard" ? 8 : 5
  );
  const deadline = performance.now() + Math.max(50, Number(timeLimitMs) || 700);
  const tt = new Map();
  const counter = { nodes: 0, ttHits: 0, cutoffs: 0 };
  let completedDepth = 0;
  let timedOut = false;
  let bestMove = moves[0];
  let bestScore = -Infinity;

  for (let depth = 1; depth <= depthCap; depth += 1) {
    let iterationMove = bestMove;
    let iterationScore = -Infinity;
    let alpha = -Infinity;
    const ordered = orderedChildren(state, moves, rootPlayer, true);
    try {
      for (const { move, child } of ordered) {
        if (performance.now() >= deadline) throw new SearchTimeout();
        const score = searchNode(
          child,
          depth - 1,
          alpha,
          Infinity,
          rootPlayer,
          deadline,
          new Set([positionKey(state)]),
          tt,
          counter,
        );
        if (score > iterationScore) {
          iterationScore = score;
          iterationMove = move;
        }
        alpha = Math.max(alpha, iterationScore);
      }
      bestMove = iterationMove;
      bestScore = iterationScore;
      completedDepth = depth;
      if (Math.abs(bestScore) >= 1_000_000) break;
    } catch (error) {
      if (!(error instanceof SearchTimeout)) throw error;
      timedOut = true;
      break;
    }
  }

  return {
    move: bestMove,
    score: Number.isFinite(bestScore) ? bestScore : 0,
    depth: completedDepth,
    nodes: counter.nodes,
    ttHits: counter.ttHits,
    cutoffs: counter.cutoffs,
    timedOut,
  };
}
