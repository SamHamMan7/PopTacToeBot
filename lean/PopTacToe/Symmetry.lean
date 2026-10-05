import PopTacToe.Rules

namespace PopTacToe

/-- The eight linear symmetries of the square grid. -/
inductive D4 where
  | identity
  | rotate90
  | rotate180
  | rotate270
  | mirror
  | mirrorRotate90
  | mirrorRotate180
  | mirrorRotate270
  deriving BEq, DecidableEq, Repr

def d4Values : List D4 := [
  .identity,
  .rotate90,
  .rotate180,
  .rotate270,
  .mirror,
  .mirrorRotate90,
  .mirrorRotate180,
  .mirrorRotate270
]

/-- Additive inverse in a coordinate modulo eight. -/
def negate8 (coordinate : Nat) : Nat :=
  (8 - coordinate % 8) % 8

/-- Apply a linear grid symmetry around the torus origin. -/
def transformCoordinates (shape : D4) (row column : Nat) : Nat × Nat :=
  let row := row % 8
  let column := column % 8
  match shape with
  | .identity => (row, column)
  | .rotate90 => (column, negate8 row)
  | .rotate180 => (negate8 row, negate8 column)
  | .rotate270 => (negate8 column, row)
  | .mirror => (row, negate8 column)
  | .mirrorRotate90 => (negate8 column, negate8 row)
  | .mirrorRotate180 => (negate8 row, column)
  | .mirrorRotate270 => (column, row)

def transformSquareD4 (shape : D4) (square : Square) : Square :=
  let transformed := transformCoordinates shape
    (square.val / 8) (square.val % 8)
  cell transformed.1 transformed.2

/-- A torus spatial symmetry is a D4 map followed by a translation. -/
structure TorusSymmetry where
  shape : D4
  rowShift : Fin 8
  columnShift : Fin 8
  deriving BEq, DecidableEq, Repr

def identitySymmetry : TorusSymmetry :=
  ⟨.identity, 0, 0⟩

/-- Exactly the 8 * 8 * 8 = 512 spatial transformations used by the solver. -/
def allTorusSymmetries : List TorusSymmetry :=
  d4Values.flatMap fun shape =>
    (List.finRange 8).flatMap fun rowShift =>
      (List.finRange 8).map fun columnShift =>
        ⟨shape, rowShift, columnShift⟩

def transformSquare (symmetry : TorusSymmetry) (square : Square) : Square :=
  let shaped := transformSquareD4 symmetry.shape square
  cell
    (shaped.val / 8 + symmetry.rowShift.val)
    (shaped.val % 8 + symmetry.columnShift.val)

def inverseD4 : D4 → D4
  | .identity => .identity
  | .rotate90 => .rotate270
  | .rotate180 => .rotate180
  | .rotate270 => .rotate90
  | .mirror => .mirror
  | .mirrorRotate90 => .mirrorRotate90
  | .mirrorRotate180 => .mirrorRotate180
  | .mirrorRotate270 => .mirrorRotate270

/-- Inverse of `x |-> A*x + shift`: `x |-> A^-1*x - A^-1*shift`. -/
def inverseSymmetry (symmetry : TorusSymmetry) : TorusSymmetry :=
  let inverseShape := inverseD4 symmetry.shape
  let negativeShift := cell
    (negate8 symmetry.rowShift.val)
    (negate8 symmetry.columnShift.val)
  let pulledBack := transformSquareD4 inverseShape negativeShift
  {
    shape := inverseShape
    rowShift := Fin.ofNat 8 (pulledBack.val / 8)
    columnShift := Fin.ofNat 8 (pulledBack.val % 8)
  }

def generatorSymmetries : List TorusSymmetry :=
  (d4Values.map fun shape =>
    { shape := shape, rowShift := 0, columnShift := 0 }) ++ [
      { shape := .identity, rowShift := 1, columnShift := 0 },
      { shape := .identity, rowShift := 0, columnShift := 1 }
    ]

def generatorInverseSquareCheck : Bool :=
  generatorSymmetries.all fun symmetry =>
    (List.finRange 64).all fun square =>
      transformSquare (inverseSymmetry symmetry)
        (transformSquare symmetry square) == square

def allInverseOriginCheck : Bool :=
  allTorusSymmetries.all fun symmetry =>
    transformSquare (inverseSymmetry symmetry)
      (transformSquare symmetry (cell 0 0)) == cell 0 0

def squareOrbit (square : Square) : List Square :=
  (allTorusSymmetries.map fun symmetry =>
    transformSquare symmetry square).eraseDups

def flipDelta : Delta → Delta
  | .negative => .positive
  | .zero => .zero
  | .positive => .negative

/-- Translation does not affect directions, so only the D4 component acts. -/
def transformDirection (shape : D4) (direction : Direction) : Direction :=
  match shape with
  | .identity => direction
  | .rotate90 => ⟨direction.column, flipDelta direction.row⟩
  | .rotate180 => ⟨flipDelta direction.row, flipDelta direction.column⟩
  | .rotate270 => ⟨flipDelta direction.column, direction.row⟩
  | .mirror => ⟨direction.row, flipDelta direction.column⟩
  | .mirrorRotate90 =>
      ⟨flipDelta direction.column, flipDelta direction.row⟩
  | .mirrorRotate180 => ⟨flipDelta direction.row, direction.column⟩
  | .mirrorRotate270 => ⟨direction.column, direction.row⟩

def generatorDisplacementCheck (distance : Nat) : Bool :=
  generatorSymmetries.all fun symmetry =>
    (List.finRange 64).all fun center =>
      pushDirections.all fun direction =>
        transformSquare symmetry (displaced center direction distance) ==
          displaced (transformSquare symmetry center)
            (transformDirection symmetry.shape direction) distance

/-- Transport a bitboard by enumerating its occupied source squares. -/
def transformBoard (symmetry : TorusSymmetry) (pieces : Board) : Board :=
  (List.finRange 64).foldl (fun transformed source =>
    if contains pieces source then
      transformed ||| bit (transformSquare symmetry source)
    else
      transformed) (0 : Board)

def transformState (symmetry : TorusSymmetry) (state : State) : State := {
  blue := transformBoard symmetry state.blue
  red := transformBoard symmetry state.red
  blueBin := state.blueBin
  redBin := state.redBin
  turn := state.turn
}

def inverseBoardCheck (pieces : Board) : Bool :=
  generatorSymmetries.all fun symmetry =>
    transformBoard (inverseSymmetry symmetry)
      (transformBoard symmetry pieces) == pieces

def symmetryProbeBoard : Board := boardOf [
  cell 0 0,
  cell 0 7,
  cell 2 5,
  cell 3 3,
  cell 6 1,
  cell 7 4
]

theorem torus_symmetry_count :
    allTorusSymmetries.length = 512 := by
  decide +kernel

theorem torus_symmetries_are_distinct :
    allTorusSymmetries.eraseDups.length = 512 := by
  decide +kernel

theorem first_square_orbit_is_the_board :
    (squareOrbit (cell 0 0)).length = 64 := by
  decide +kernel

theorem generator_inverse_square_check_passes :
    generatorInverseSquareCheck = true := by
  decide +kernel

theorem all_inverse_origin_checks_pass :
    allInverseOriginCheck = true := by
  decide +kernel

theorem generator_distance_one_geometry_is_equivariant :
    generatorDisplacementCheck 1 = true := by
  decide +kernel

theorem generator_distance_two_geometry_is_equivariant :
    generatorDisplacementCheck 2 = true := by
  decide +kernel

theorem probe_board_round_trips :
    inverseBoardCheck symmetryProbeBoard = true := by
  decide +kernel

#print axioms torus_symmetry_count
#print axioms generator_inverse_square_check_passes
#print axioms all_inverse_origin_checks_pass
#print axioms generator_distance_one_geometry_is_equivariant
#print axioms probe_board_round_trips

end PopTacToe