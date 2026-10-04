import PopTacToe.Equivariance

namespace PopTacToe

abbrev Coordinate := Fin 8
abbrev Coordinates := Coordinate × Coordinate

def coordinatePairs : List Coordinates :=
  (List.finRange 8).flatMap fun row =>
    (List.finRange 8).map fun column => (row, column)

def deltaValues : List Delta := [.negative, .zero, .positive]

def allDirections : List Direction :=
  deltaValues.flatMap fun row =>
    deltaValues.map fun column => ⟨row, column⟩

def squareCoordinates (square : Square) : Coordinates :=
  (Fin.ofNat 8 (square.val / 8), Fin.ofNat 8 (square.val % 8))

def squareOfCoordinates (coordinates : Coordinates) : Square :=
  cell coordinates.1.val coordinates.2.val

def addCoordinates (left right : Coordinates) : Coordinates :=
  (left.1 + right.1, left.2 + right.2)

def deltaCoordinate : Delta → Coordinate
  | .negative => 7
  | .zero => 0
  | .positive => 1

def directionVector (direction : Direction) (distance : Nat) : Coordinates :=
  (Fin.ofNat 8 distance * deltaCoordinate direction.row,
    Fin.ofNat 8 distance * deltaCoordinate direction.column)

def advanceCoordinates (coordinates : Coordinates) (direction : Direction)
    (distance : Nat) : Coordinates :=
  addCoordinates coordinates (directionVector direction distance)

def shapeCoordinates (shape : D4) (coordinates : Coordinates) : Coordinates :=
  match shape with
  | .identity => coordinates
  | .rotate90 => (coordinates.2, -coordinates.1)
  | .rotate180 => (-coordinates.1, -coordinates.2)
  | .rotate270 => (-coordinates.2, coordinates.1)
  | .mirror => (coordinates.1, -coordinates.2)
  | .mirrorRotate90 => (-coordinates.2, -coordinates.1)
  | .mirrorRotate180 => (-coordinates.1, coordinates.2)
  | .mirrorRotate270 => (coordinates.2, coordinates.1)

def symmetryCoordinates (symmetry : TorusSymmetry)
    (coordinates : Coordinates) : Coordinates :=
  addCoordinates (shapeCoordinates symmetry.shape coordinates)
    (symmetry.rowShift, symmetry.columnShift)

def squareCoordinateRoundTripCheck : Bool :=
  (List.finRange 64).all fun square =>
    squareOfCoordinates (squareCoordinates square) == square

def coordinateSquareRoundTripCheck : Bool :=
  coordinatePairs.all fun coordinates =>
    squareCoordinates (squareOfCoordinates coordinates) == coordinates

def transformSquareModelCheck : Bool :=
  allTorusSymmetries.all fun symmetry =>
    (List.finRange 64).all fun square =>
      transformSquare symmetry square ==
        squareOfCoordinates (symmetryCoordinates symmetry
          (squareCoordinates square))

def displacedModelCheck : Bool :=
  (List.finRange 64).all fun square =>
    allDirections.all fun direction =>
      ([1, 2] : List Nat).all fun distance =>
        displaced square direction distance ==
          squareOfCoordinates
            (advanceCoordinates (squareCoordinates square) direction distance)

def shapeAdvanceCheck : Bool :=
  d4Values.all fun shape =>
    coordinatePairs.all fun coordinates =>
      allDirections.all fun direction =>
        ([1, 2] : List Nat).all fun distance =>
          shapeCoordinates shape
              (advanceCoordinates coordinates direction distance) ==
            advanceCoordinates (shapeCoordinates shape coordinates)
              (transformDirection shape direction) distance

def coordinateTranslationCheck : Bool :=
  (List.finRange 8).all fun coordinate =>
    (List.finRange 8).all fun shift =>
      deltaValues.all fun delta =>
        ([1, 2] : List Nat).all fun distance =>
          (coordinate + Fin.ofNat 8 distance * deltaCoordinate delta) + shift ==
            (coordinate + shift) +
              Fin.ofNat 8 distance * deltaCoordinate delta

def directionInverseCheck : Bool :=
  d4Values.all fun shape =>
    allDirections.all fun direction =>
      (decide (transformDirection (inverseD4 shape)
        (transformDirection shape direction) = direction)) &&
      (decide (transformDirection shape
        (transformDirection (inverseD4 shape) direction) = direction))

theorem every_d4_member (shape : D4) : shape ∈ d4Values := by
  cases shape <;> simp [d4Values]

theorem every_delta_member (delta : Delta) : delta ∈ deltaValues := by
  cases delta <;> simp [deltaValues]

theorem every_direction_member (direction : Direction) :
    direction ∈ allDirections := by
  rcases direction with ⟨row, column⟩
  cases row <;> cases column <;> simp [allDirections, deltaValues]

theorem every_coordinate_pair_member (coordinates : Coordinates) :
    coordinates ∈ coordinatePairs := by
  rcases coordinates with ⟨row, column⟩
  simp [coordinatePairs, List.mem_finRange]

theorem square_coordinate_round_trip_check_passes :
    squareCoordinateRoundTripCheck = true := by
  decide +kernel

theorem coordinate_square_round_trip_check_passes :
    coordinateSquareRoundTripCheck = true := by
  decide +kernel

theorem transformSquare_model_check_passes :
    transformSquareModelCheck = true := by
  decide +kernel

theorem displaced_model_check_passes : displacedModelCheck = true := by
  decide +kernel

theorem shape_advance_check_passes : shapeAdvanceCheck = true := by
  decide +kernel

theorem coordinate_translation_check_passes :
    coordinateTranslationCheck = true := by
  decide +kernel

theorem direction_inverse_check_passes : directionInverseCheck = true := by
  decide +kernel

theorem squareOf_squareCoordinates (square : Square) :
    squareOfCoordinates (squareCoordinates square) = square := by
  have checked := square_coordinate_round_trip_check_passes
  simp only [squareCoordinateRoundTripCheck, List.all_eq_true] at checked
  exact eq_of_beq (checked square (List.mem_finRange square))

theorem squareCoordinates_squareOf (coordinates : Coordinates) :
    squareCoordinates (squareOfCoordinates coordinates) = coordinates := by
  have checked := coordinate_square_round_trip_check_passes
  simp only [coordinateSquareRoundTripCheck, List.all_eq_true] at checked
  exact eq_of_beq
    (checked coordinates (every_coordinate_pair_member coordinates))

theorem transformSquare_model (symmetry : TorusSymmetry) (square : Square) :
    transformSquare symmetry square =
      squareOfCoordinates (symmetryCoordinates symmetry
        (squareCoordinates square)) := by
  have checked := transformSquare_model_check_passes
  simp only [transformSquareModelCheck, List.all_eq_true] at checked
  exact eq_of_beq (checked symmetry (all_symmetries_member symmetry)
    square (List.mem_finRange square))

theorem displaced_model (square : Square) (direction : Direction)
    (distance : Nat) (distanceMember : distance ∈ ([1, 2] : List Nat)) :
    displaced square direction distance =
      squareOfCoordinates
        (advanceCoordinates (squareCoordinates square) direction distance) := by
  have checked := displaced_model_check_passes
  simp only [displacedModelCheck, List.all_eq_true] at checked
  exact eq_of_beq (checked square (List.mem_finRange square)
    direction (every_direction_member direction) distance distanceMember)

theorem shape_advance (shape : D4) (coordinates : Coordinates)
    (direction : Direction) (distance : Nat)
    (distanceMember : distance ∈ ([1, 2] : List Nat)) :
    shapeCoordinates shape (advanceCoordinates coordinates direction distance) =
      advanceCoordinates (shapeCoordinates shape coordinates)
        (transformDirection shape direction) distance := by
  have checked := shape_advance_check_passes
  simp only [shapeAdvanceCheck, List.all_eq_true] at checked
  exact eq_of_beq (checked shape (every_d4_member shape)
    coordinates (every_coordinate_pair_member coordinates)
    direction (every_direction_member direction) distance distanceMember)

theorem advance_coordinate_translation (coordinate shift : Coordinate)
    (delta : Delta) (distance : Nat)
    (distanceMember : distance ∈ ([1, 2] : List Nat)) :
    (coordinate + Fin.ofNat 8 distance * deltaCoordinate delta) + shift =
      (coordinate + shift) + Fin.ofNat 8 distance * deltaCoordinate delta := by
  have checked := coordinate_translation_check_passes
  simp only [coordinateTranslationCheck, List.all_eq_true] at checked
  exact eq_of_beq (checked coordinate (List.mem_finRange coordinate)
    shift (List.mem_finRange shift) delta (every_delta_member delta)
    distance distanceMember)

theorem advance_coordinates_translation (coordinates shift : Coordinates)
    (direction : Direction) (distance : Nat)
    (distanceMember : distance ∈ ([1, 2] : List Nat)) :
    addCoordinates (advanceCoordinates coordinates direction distance) shift =
      advanceCoordinates (addCoordinates coordinates shift) direction distance := by
  apply Prod.ext
  · exact advance_coordinate_translation coordinates.1 shift.1 direction.row
      distance distanceMember
  · exact advance_coordinate_translation coordinates.2 shift.2 direction.column
      distance distanceMember

theorem inverse_transformDirection (shape : D4) (direction : Direction) :
    transformDirection (inverseD4 shape)
      (transformDirection shape direction) = direction := by
  have checked := direction_inverse_check_passes
  simp only [directionInverseCheck, List.all_eq_true] at checked
  have pair := checked shape (every_d4_member shape)
    direction (every_direction_member direction)
  simp only [Bool.and_eq_true] at pair
  exact of_decide_eq_true pair.1

theorem transformDirection_inverse (shape : D4) (direction : Direction) :
    transformDirection shape
      (transformDirection (inverseD4 shape) direction) = direction := by
  have checked := direction_inverse_check_passes
  simp only [directionInverseCheck, List.all_eq_true] at checked
  have pair := checked shape (every_d4_member shape)
    direction (every_direction_member direction)
  simp only [Bool.and_eq_true] at pair
  exact of_decide_eq_true pair.2

theorem transformDirection_push_member (shape : D4) (direction : Direction)
    (member : direction ∈ pushDirections) :
    transformDirection shape direction ∈ pushDirections := by
  rcases direction with ⟨row, column⟩
  cases shape <;> cases row <;> cases column <;>
    simp [pushDirections, transformDirection, flipDelta] at member ⊢

theorem symmetry_advance (symmetry : TorusSymmetry)
    (coordinates : Coordinates) (direction : Direction) (distance : Nat)
    (distanceMember : distance ∈ ([1, 2] : List Nat)) :
    symmetryCoordinates symmetry
        (advanceCoordinates coordinates direction distance) =
      advanceCoordinates (symmetryCoordinates symmetry coordinates)
        (transformDirection symmetry.shape direction) distance := by
  unfold symmetryCoordinates
  rw [shape_advance (shape := symmetry.shape) (coordinates := coordinates)
    (direction := direction) (distance := distance) distanceMember]
  exact advance_coordinates_translation
    (shapeCoordinates symmetry.shape coordinates)
    (symmetry.rowShift, symmetry.columnShift)
    (transformDirection symmetry.shape direction) distance distanceMember

/-- All 512 torus symmetries preserve the distance-one pop source. -/
theorem displaced_transform_one (symmetry : TorusSymmetry)
    (center : Square) (direction : Direction) :
    transformSquare symmetry (displaced center direction 1) =
      displaced (transformSquare symmetry center)
        (transformDirection symmetry.shape direction) 1 := by
  calc
    transformSquare symmetry (displaced center direction 1) =
        squareOfCoordinates
          (symmetryCoordinates symmetry
            (squareCoordinates (displaced center direction 1))) :=
      transformSquare_model symmetry _
    _ = squareOfCoordinates
          (symmetryCoordinates symmetry
            (advanceCoordinates (squareCoordinates center) direction 1)) := by
      rw [displaced_model center direction 1 (by decide),
        squareCoordinates_squareOf]
    _ = squareOfCoordinates
          (advanceCoordinates
            (symmetryCoordinates symmetry (squareCoordinates center))
            (transformDirection symmetry.shape direction) 1) := by
      rw [symmetry_advance symmetry (squareCoordinates center) direction 1
        (by decide)]
    _ = squareOfCoordinates
          (advanceCoordinates
            (squareCoordinates (transformSquare symmetry center))
            (transformDirection symmetry.shape direction) 1) := by
      rw [transformSquare_model symmetry center,
        squareCoordinates_squareOf]
    _ = displaced (transformSquare symmetry center)
          (transformDirection symmetry.shape direction) 1 :=
      (displaced_model _ _ 1 (by decide)).symm

/-- All 512 torus symmetries preserve the distance-two pop destination. -/
theorem displaced_transform_two (symmetry : TorusSymmetry)
    (center : Square) (direction : Direction) :
    transformSquare symmetry (displaced center direction 2) =
      displaced (transformSquare symmetry center)
        (transformDirection symmetry.shape direction) 2 := by
  calc
    transformSquare symmetry (displaced center direction 2) =
        squareOfCoordinates
          (symmetryCoordinates symmetry
            (squareCoordinates (displaced center direction 2))) :=
      transformSquare_model symmetry _
    _ = squareOfCoordinates
          (symmetryCoordinates symmetry
            (advanceCoordinates (squareCoordinates center) direction 2)) := by
      rw [displaced_model center direction 2 (by decide),
        squareCoordinates_squareOf]
    _ = squareOfCoordinates
          (advanceCoordinates
            (symmetryCoordinates symmetry (squareCoordinates center))
            (transformDirection symmetry.shape direction) 2) := by
      rw [symmetry_advance symmetry (squareCoordinates center) direction 2
        (by decide)]
    _ = squareOfCoordinates
          (advanceCoordinates
            (squareCoordinates (transformSquare symmetry center))
            (transformDirection symmetry.shape direction) 2) := by
      rw [transformSquare_model symmetry center,
        squareCoordinates_squareOf]
    _ = displaced (transformSquare symmetry center)
          (transformDirection symmetry.shape direction) 2 :=
      (displaced_model _ _ 2 (by decide)).symm

#print axioms transformSquare_model
#print axioms displaced_transform_one
#print axioms displaced_transform_two
#print axioms inverse_transformDirection
#print axioms transformDirection_push_member

end PopTacToe