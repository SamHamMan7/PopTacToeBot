import assert from "node:assert/strict";
import {
  AllOnBoardRule,
  EdgeRule,
  MoveHowRule,
  MoveKind,
  MoveWhenRule,
  Outcome,
  Player,
  applyMove,
  applyPopMechanic,
  chooseComputerMove,
  legalMoves,
  makeState,
  positionKey,
  square,
  terminalOutcome,
} from "./engine.mjs";

function rulesFor(edge, checkers = 8) {
  return {
    blueCheckers: checkers,
    redCheckers: checkers,
    edge,
    allOnBoard: AllOnBoardRule.CONTINUE,
    moveWhen: MoveWhenRule.ALL_ON_BOARD,
    moveHow: MoveHowRule.KING,
    zeroMoveAllowed: false,
    jumpsAllowed: false,
  };
}

function piece(player, row, column) {
  return { player, row, column };
}

function cell(state, row, column) {
  return state.board[square(row, column)];
}

function pop(state, row, column) {
  return applyPopMechanic(state, square(row, column)).state;
}

{
  let state = makeState({
    rules: rulesFor(EdgeRule.REINCARNATION),
    pieces: [piece(Player.RED, 3, 4)],
  });
  state = pop(state, 3, 3);
  assert.equal(cell(state, 3, 4), Player.NONE);
  assert.equal(cell(state, 3, 5), Player.RED);
}

{
  let state = makeState({
    rules: rulesFor(EdgeRule.REINCARNATION),
    pieces: [piece(Player.BLUE, 3, 4), piece(Player.RED, 3, 5)],
  });
  state = pop(state, 3, 3);
  assert.equal(cell(state, 3, 4), Player.BLUE);
  assert.equal(cell(state, 3, 5), Player.RED);
}

{
  let state = makeState({
    rules: rulesFor(EdgeRule.REINCARNATION),
    pieces: [
      piece(Player.BLUE, 2, 2),
      piece(Player.RED, 2, 3),
      piece(Player.BLUE, 2, 4),
      piece(Player.RED, 3, 2),
      piece(Player.BLUE, 3, 4),
      piece(Player.RED, 4, 2),
      piece(Player.BLUE, 4, 3),
      piece(Player.RED, 4, 4),
    ],
  });
  state = pop(state, 3, 3);
  const expected = [
    piece(Player.BLUE, 1, 1),
    piece(Player.RED, 1, 3),
    piece(Player.BLUE, 1, 5),
    piece(Player.RED, 3, 1),
    piece(Player.BLUE, 3, 5),
    piece(Player.RED, 5, 1),
    piece(Player.BLUE, 5, 3),
    piece(Player.RED, 5, 5),
  ];
  for (const item of expected) assert.equal(cell(state, item.row, item.column), item.player);
}

{
  let state = makeState({
    rules: rulesFor(EdgeRule.REINCARNATION, 3),
    pieces: [piece(Player.RED, 0, 0)],
  });
  const before = state.redBin;
  state = pop(state, 0, 1);
  assert.equal(cell(state, 0, 0), Player.NONE);
  assert.equal(state.redBin, before + 1);
  assert.equal(state.blueBin, 3);
}

{
  let state = makeState({
    rules: rulesFor(EdgeRule.TORUS, 3),
    pieces: [piece(Player.RED, 0, 0)],
  });
  state = pop(state, 0, 1);
  assert.equal(cell(state, 0, 0), Player.NONE);
  assert.equal(cell(state, 0, 7), Player.RED);
}

{
  let state = makeState({
    rules: rulesFor(EdgeRule.KLEIN, 3),
    pieces: [piece(Player.BLUE, 0, 1)],
  });
  state = pop(state, 1, 1);
  assert.equal(cell(state, 0, 1), Player.NONE);
  assert.equal(cell(state, 7, 6), Player.BLUE);
}

{
  let state = makeState({
    rules: rulesFor(EdgeRule.REINCARNATION, 4),
    pieces: [
      piece(Player.BLUE, 3, 4),
      piece(Player.BLUE, 3, 6),
      piece(Player.BLUE, 3, 7),
    ],
    nextPlayer: Player.BLUE,
  });
  state = applyMove(state, { kind: MoveKind.PLACE, from: null, to: square(3, 3) });
  assert.equal(cell(state, 3, 4), Player.NONE);
  assert.equal(cell(state, 3, 5), Player.BLUE);
  assert.equal(terminalOutcome(state), Outcome.BLUE_WIN);
}

{
  let state = makeState({
    rules: rulesFor(EdgeRule.REINCARNATION, 3),
    pieces: [piece(Player.BLUE, 3, 2), piece(Player.BLUE, 3, 4)],
    nextPlayer: Player.BLUE,
  });
  state = applyMove(state, { kind: MoveKind.PLACE, from: null, to: square(3, 3) });
  assert.equal(cell(state, 3, 1), Player.BLUE);
  assert.equal(cell(state, 3, 5), Player.BLUE);
  assert.equal(terminalOutcome(state), Outcome.ONGOING);
}

{
  const state = makeState({
    rules: rulesFor(EdgeRule.REINCARNATION, 3),
    pieces: [
      piece(Player.BLUE, 0, 0),
      piece(Player.BLUE, 0, 1),
      piece(Player.BLUE, 0, 2),
      piece(Player.RED, 7, 5),
      piece(Player.RED, 7, 6),
      piece(Player.RED, 7, 7),
    ],
  });
  assert.equal(terminalOutcome(state), Outcome.DRAW);
}

{
  const state = makeState({
    rules: rulesFor(EdgeRule.TORUS, 3),
    pieces: [
      piece(Player.BLUE, 2, 7),
      piece(Player.BLUE, 2, 0),
      piece(Player.BLUE, 2, 1),
    ],
  });
  assert.equal(terminalOutcome(state), Outcome.BLUE_WIN);
}

{
  let state = makeState({
    rules: rulesFor(EdgeRule.REINCARNATION, 3),
    pieces: [piece(Player.BLUE, 2, 2)],
    nextPlayer: Player.BLUE,
  });
  assert.ok(legalMoves(state).every((move) => move.kind === MoveKind.PLACE));

  state = makeState({
    rules: rulesFor(EdgeRule.REINCARNATION, 3),
    pieces: [
      piece(Player.BLUE, 0, 0),
      piece(Player.BLUE, 3, 3),
      piece(Player.BLUE, 7, 7),
    ],
    nextPlayer: Player.BLUE,
  });
  assert.ok(legalMoves(state).length > 0);
  assert.ok(legalMoves(state).every((move) => move.kind === MoveKind.MOVE));
}

{
  let state = makeState({
    rules: rulesFor(EdgeRule.REINCARNATION, 3),
    pieces: [
      piece(Player.BLUE, 0, 0),
      piece(Player.BLUE, 3, 3),
      piece(Player.BLUE, 7, 7),
      piece(Player.RED, 3, 5),
    ],
    nextPlayer: Player.BLUE,
  });
  state = applyMove(state, {
    kind: MoveKind.MOVE,
    from: square(3, 3),
    to: square(3, 4),
  });
  assert.equal(cell(state, 3, 3), Player.NONE);
  assert.equal(cell(state, 3, 4), Player.BLUE);
  assert.equal(cell(state, 3, 5), Player.NONE);
  assert.equal(cell(state, 3, 6), Player.RED);
}

{
  const first = makeState({
    rules: rulesFor(EdgeRule.TORUS, 3),
    pieces: [piece(Player.BLUE, 1, 1), piece(Player.RED, 4, 4)],
    nextPlayer: Player.BLUE,
    ply: 10,
  });
  const same = { ...first, board: [...first.board], labels: [...first.labels], ply: 500 };
  assert.equal(positionKey(first), positionKey(same));
  same.nextPlayer = Player.RED;
  assert.notEqual(positionKey(first), positionKey(same));
}

{
  const state = makeState({
    rules: rulesFor(EdgeRule.TORUS, 4),
    pieces: [
      piece(Player.RED, 3, 4),
      piece(Player.RED, 3, 6),
      piece(Player.RED, 3, 7),
    ],
    nextPlayer: Player.RED,
  });
  const result = chooseComputerMove(state, { difficulty: "medium", timeLimitMs: 200 });
  const child = applyMove(state, result.move);
  assert.equal(terminalOutcome(child), Outcome.RED_WIN);
}

console.log("All browser engine tests passed.");
