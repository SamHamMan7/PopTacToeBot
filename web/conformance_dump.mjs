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
  makeState,
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

const piece = (player, row, column) => ({ player, row, column });

function outcomeName(outcome) {
  switch (outcome) {
    case Outcome.BLUE_WIN: return "blueWin";
    case Outcome.RED_WIN: return "redWin";
    case Outcome.DRAW: return "draw";
    default: return "ongoing";
  }
}

function emit(id, state) {
  const board = state.board.map((cell) => (
    cell === Player.BLUE ? "B" : cell === Player.RED ? "R" : "."
  )).join("");
  const next = state.nextPlayer === Player.BLUE ? "blue" : "red";
  console.log([
    id,
    board,
    state.blueBin,
    state.redBin,
    next,
    state.ply,
    outcomeName(terminalOutcome(state)),
  ].join("|"));
}

{
  let s = makeState({
    rules: rulesFor(EdgeRule.REINCARNATION),
    pieces: [piece(Player.RED, 3, 4)],
  });
  s = applyPopMechanic(s, square(3, 3)).state;
  emit("adjacent", s);
}

{
  let s = makeState({
    rules: rulesFor(EdgeRule.REINCARNATION),
    pieces: [piece(Player.BLUE, 3, 4), piece(Player.RED, 3, 5)],
  });
  s = applyPopMechanic(s, square(3, 3)).state;
  emit("blocked", s);
}

{
  let s = makeState({
    rules: rulesFor(EdgeRule.REINCARNATION),
    pieces: [
      piece(Player.BLUE, 2, 2), piece(Player.RED, 2, 3),
      piece(Player.BLUE, 2, 4), piece(Player.RED, 3, 2),
      piece(Player.BLUE, 3, 4), piece(Player.RED, 4, 2),
      piece(Player.BLUE, 4, 3), piece(Player.RED, 4, 4),
    ],
  });
  s = applyPopMechanic(s, square(3, 3)).state;
  emit("eight", s);
}

{
  let s = makeState({
    rules: rulesFor(EdgeRule.REINCARNATION, 3),
    pieces: [piece(Player.RED, 0, 0)],
  });
  s = applyPopMechanic(s, square(0, 1)).state;
  emit("reincarnate", s);
}

{
  let s = makeState({
    rules: rulesFor(EdgeRule.TORUS, 3),
    pieces: [piece(Player.RED, 0, 0)],
  });
  s = applyPopMechanic(s, square(0, 1)).state;
  emit("torus", s);
}

{
  let s = makeState({
    rules: rulesFor(EdgeRule.KLEIN, 3),
    pieces: [piece(Player.BLUE, 0, 1)],
  });
  s = applyPopMechanic(s, square(1, 1)).state;
  emit("klein", s);
}

{
  let s = makeState({
    rules: rulesFor(EdgeRule.REINCARNATION, 4),
    pieces: [
      piece(Player.BLUE, 3, 4),
      piece(Player.BLUE, 3, 6),
      piece(Player.BLUE, 3, 7),
    ],
    nextPlayer: Player.BLUE,
  });
  s = applyMove(s, { kind: MoveKind.PLACE, from: null, to: square(3, 3) });
  emit("postpopwin", s);
}

{
  let s = makeState({
    rules: rulesFor(EdgeRule.REINCARNATION, 3),
    pieces: [piece(Player.BLUE, 3, 2), piece(Player.BLUE, 3, 4)],
    nextPlayer: Player.BLUE,
  });
  s = applyMove(s, { kind: MoveKind.PLACE, from: null, to: square(3, 3) });
  emit("prepop", s);
}

{
  const s = makeState({
    rules: rulesFor(EdgeRule.REINCARNATION, 3),
    pieces: [
      piece(Player.BLUE, 0, 0), piece(Player.BLUE, 0, 1),
      piece(Player.BLUE, 0, 2), piece(Player.RED, 7, 5),
      piece(Player.RED, 7, 6), piece(Player.RED, 7, 7),
    ],
  });
  emit("simdraw", s);
}

{
  const s = makeState({
    rules: rulesFor(EdgeRule.TORUS, 3),
    pieces: [
      piece(Player.BLUE, 2, 7),
      piece(Player.BLUE, 2, 0),
      piece(Player.BLUE, 2, 1),
    ],
  });
  emit("torusline", s);
}

{
  let s = makeState({
    rules: rulesFor(EdgeRule.REINCARNATION, 3),
    pieces: [
      piece(Player.BLUE, 0, 0),
      piece(Player.BLUE, 3, 3),
      piece(Player.BLUE, 7, 7),
      piece(Player.RED, 3, 5),
    ],
    nextPlayer: Player.BLUE,
  });
  s = applyMove(s, {
    kind: MoveKind.MOVE,
    from: square(3, 3),
    to: square(3, 4),
  });
  emit("travelpop", s);
}
