import Std

namespace PopTacToe

abbrev Board := BitVec 64
abbrev Square := Fin 64

inductive Player where
  | blue
  | red
  deriving BEq, DecidableEq, Repr

def Player.other : Player → Player
  | .blue => .red
  | .red => .blue

inductive Outcome where
  | ongoing
  | blueWin
  | redWin
  | draw
  deriving BEq, DecidableEq, Repr

structure State where
  blue : Board := 0
  red : Board := 0
  blueBin : Nat := 8
  redBin : Nat := 8
  turn : Player := .blue
  deriving BEq, DecidableEq, Repr

def State.occupied (state : State) : Board := state.blue ||| state.red

def State.moverBin (state : State) : Nat :=
  match state.turn with
  | .blue => state.blueBin
  | .red => state.redBin

def bit (cell : Square) : Board := BitVec.ofNat 64 (1 <<< cell.val)

def boardOf (cells : List Square) : Board :=
  cells.foldl (fun pieces cell => pieces ||| bit cell) 0

def contains (pieces : Board) (cell : Square) : Bool :=
  pieces.getLsbD cell.val

def emptyAt (state : State) (cell : Square) : Bool :=
  !(contains state.occupied cell)

inductive Delta where
  | negative
  | zero
  | positive
  deriving BEq, DecidableEq, Repr

structure Direction where
  row : Delta
  column : Delta
  deriving BEq, DecidableEq, Repr

def pushDirections : List Direction := [
  ⟨.negative, .negative⟩,
  ⟨.negative, .zero⟩,
  ⟨.negative, .positive⟩,
  ⟨.zero, .negative⟩,
  ⟨.zero, .positive⟩,
  ⟨.positive, .negative⟩,
  ⟨.positive, .zero⟩,
  ⟨.positive, .positive⟩
]

def lineDirections : List Direction := [
  ⟨.zero, .positive⟩,
  ⟨.positive, .zero⟩,
  ⟨.positive, .positive⟩,
  ⟨.positive, .negative⟩
]

def shiftCoordinate (distance coordinate : Nat) : Delta → Nat
  | .negative => (coordinate + 8 - distance % 8) % 8
  | .zero => coordinate % 8
  | .positive => (coordinate + distance) % 8

def displaced (center : Square) (direction : Direction)
    (distance : Nat) : Square :=
  let row := center.val / 8
  let column := center.val % 8
  Fin.ofNat 64
    (shiftCoordinate distance row direction.row * 8 +
      shiftCoordinate distance column direction.column)

structure Pushes where
  clear : Board := 0
  addBlue : Board := 0
  addRed : Board := 0

def collectPush (snapshotBlue snapshotRed : Board) (center : Square)
    (pushes : Pushes) (direction : Direction) : Pushes :=
  let source := displaced center direction 1
  let destination := displaced center direction 2
  let occupied := snapshotBlue ||| snapshotRed
  if contains occupied source && !(contains occupied destination) then
    if contains snapshotBlue source then
      { pushes with
        clear := pushes.clear ||| bit source
        addBlue := pushes.addBlue ||| bit destination }
    else
      { pushes with
        clear := pushes.clear ||| bit source
        addRed := pushes.addRed ||| bit destination }
  else
    pushes

def resolvePops (placedBlue placedRed : Board) (target : Square) : Board × Board :=
  let pushes := pushDirections.foldl
    (collectPush placedBlue placedRed target) {}
  ((placedBlue &&& ~~~pushes.clear) ||| pushes.addBlue,
    (placedRed &&& ~~~pushes.clear) ||| pushes.addRed)

def applyPlacement (state : State) (target : Square) : State :=
  match state.turn with
  | .blue =>
      let boards := resolvePops (state.blue ||| bit target) state.red target
      {
        blue := boards.1
        red := boards.2
        blueBin := state.blueBin - 1
        redBin := state.redBin
        turn := .red
      }
  | .red =>
      let boards := resolvePops state.blue (state.red ||| bit target) target
      {
        blue := boards.1
        red := boards.2
        blueBin := state.blueBin
        redBin := state.redBin - 1
        turn := .blue
      }

def legalPlacement (state : State) (target : Square) : Bool :=
  decide (0 < state.moverBin) && emptyAt state target

def LegalPlacement (state : State) (target : Square) : Prop :=
  legalPlacement state target = true

instance (state : State) (target : Square) :
    Decidable (LegalPlacement state target) := by
  unfold LegalPlacement
  infer_instance

def lineAt (pieces : Board) (start : Square)
    (direction : Direction) : Bool :=
  contains pieces start &&
    contains pieces (displaced start direction 1) &&
    contains pieces (displaced start direction 2)

def hasTorusLine (pieces : Board) : Bool :=
  (List.finRange 64).any fun start =>
    lineDirections.any (lineAt pieces start)

def outcome (state : State) : Outcome :=
  match hasTorusLine state.blue, hasTorusLine state.red with
  | true, true => .draw
  | true, false => .blueWin
  | false, true => .redWin
  | false, false => .ongoing

def BlueWins (state : State) : Prop := outcome state = .blueWin

instance (state : State) : Decidable (BlueWins state) := by
  unfold BlueWins
  infer_instance

def initial : State := {}

def remaining (state : State) : Nat := state.blueBin + state.redBin

def playPlacements? : State → List Square → Option State
  | state, [] => some state
  | state, target :: rest =>
      if legalPlacement state target then
        playPlacements? (applyPlacement state target) rest
      else
        none

def cell (row column : Nat) : Square :=
  Fin.ofNat 64 ((row % 8) * 8 + column % 8)

theorem remaining_applyPlacement (state : State) (target : Square)
    (positive : 0 < state.moverBin) :
    remaining (applyPlacement state target) + 1 = remaining state := by
  rcases state with ⟨blue, red, blueBin, redBin, turn⟩
  cases turn <;>
    simp [State.moverBin, remaining, applyPlacement] at positive ⊢ <;>
    omega

end PopTacToe
