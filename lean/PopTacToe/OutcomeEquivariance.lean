import PopTacToe.Geometry

namespace PopTacToe

def reverseDirection (direction : Direction) : Direction :=
  ⟨flipDelta direction.row, flipDelta direction.column⟩

def reverseLineCheck : Bool :=
  (List.finRange 64).all fun start =>
    pushDirections.all fun direction =>
      (displaced (displaced start direction 2) (reverseDirection direction) 1 ==
        displaced start direction 1) &&
      (displaced (displaced start direction 2) (reverseDirection direction) 2 ==
        start)

theorem reverse_line_check_passes : reverseLineCheck = true := by
  decide +kernel

theorem line_or_reverse_member (direction : Direction)
    (member : direction ∈ pushDirections) :
    direction ∈ lineDirections ∨ reverseDirection direction ∈ lineDirections := by
  rcases direction with ⟨row, column⟩
  cases row <;> cases column <;>
    simp [pushDirections, lineDirections, reverseDirection, flipDelta] at member ⊢

theorem lineDirection_push_member (direction : Direction)
    (member : direction ∈ lineDirections) : direction ∈ pushDirections := by
  rcases direction with ⟨row, column⟩
  cases row <;> cases column <;>
    simp [pushDirections, lineDirections] at member ⊢

theorem reverse_line_geometry (start : Square) (direction : Direction)
    (member : direction ∈ pushDirections) :
    displaced (displaced start direction 2) (reverseDirection direction) 1 =
        displaced start direction 1 ∧
      displaced (displaced start direction 2) (reverseDirection direction) 2 =
        start := by
  have checked := reverse_line_check_passes
  simp only [reverseLineCheck, List.all_eq_true] at checked
  have pair := checked start (List.mem_finRange start) direction member
  simp only [Bool.and_eq_true] at pair
  exact ⟨eq_of_beq pair.1, eq_of_beq pair.2⟩

theorem lineAt_reverse (pieces : Board) (start : Square)
    (direction : Direction) (member : direction ∈ pushDirections) :
    lineAt pieces (displaced start direction 2) (reverseDirection direction) =
      lineAt pieces start direction := by
  have geometry := reverse_line_geometry start direction member
  unfold lineAt
  rw [geometry.1, geometry.2]
  simp only [Bool.and_comm, Bool.and_assoc]

def hasAnyTorusLine (pieces : Board) : Bool :=
  (List.finRange 64).any fun start =>
    pushDirections.any (lineAt pieces start)

theorem hasAnyTorusLine_eq_hasTorusLine (pieces : Board) :
    hasAnyTorusLine pieces = hasTorusLine pieces := by
  apply Bool.eq_iff_iff.mpr
  simp only [hasAnyTorusLine, hasTorusLine, List.any_eq_true]
  constructor
  · rintro ⟨start, startMember, direction, directionMember, line⟩
    cases line_or_reverse_member direction directionMember with
    | inl canonical =>
        exact ⟨start, startMember, direction, canonical, line⟩
    | inr reversed =>
        refine ⟨displaced start direction 2,
          List.mem_finRange _, reverseDirection direction, reversed, ?_⟩
        rw [lineAt_reverse pieces start direction directionMember]
        exact line
  · rintro ⟨start, startMember, direction, directionMember, line⟩
    exact ⟨start, startMember, direction,
      lineDirection_push_member direction directionMember, line⟩

theorem lineAt_transform (symmetry : TorusSymmetry) (pieces : Board)
    (start : Square) (direction : Direction) :
    lineAt (transformBoard symmetry pieces) (transformSquare symmetry start)
        (transformDirection symmetry.shape direction) =
      lineAt pieces start direction := by
  unfold lineAt
  rw [contains_transformBoard_image,
    ← displaced_transform_one, ← displaced_transform_two,
    contains_transformBoard_image, contains_transformBoard_image]

theorem hasAnyTorusLine_forward (symmetry : TorusSymmetry)
    (pieces : Board) (line : hasAnyTorusLine pieces = true) :
    hasAnyTorusLine (transformBoard symmetry pieces) = true := by
  simp only [hasAnyTorusLine, List.any_eq_true] at line ⊢
  rcases line with ⟨start, startMember, direction, directionMember, accepted⟩
  refine ⟨transformSquare symmetry start, List.mem_finRange _,
    transformDirection symmetry.shape direction,
    transformDirection_push_member symmetry.shape direction directionMember, ?_⟩
  rw [lineAt_transform]
  exact accepted

theorem hasAnyTorusLine_transform (symmetry : TorusSymmetry)
    (pieces : Board) :
    hasAnyTorusLine (transformBoard symmetry pieces) = hasAnyTorusLine pieces := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro transformedLine
    have returned := hasAnyTorusLine_forward (inverseSymmetry symmetry)
      (transformBoard symmetry pieces) transformedLine
    rw [transformBoard_round_trip] at returned
    exact returned
  · exact hasAnyTorusLine_forward symmetry pieces

theorem hasTorusLine_transform (symmetry : TorusSymmetry) (pieces : Board) :
    hasTorusLine (transformBoard symmetry pieces) = hasTorusLine pieces := by
  rw [← hasAnyTorusLine_eq_hasTorusLine,
    ← hasAnyTorusLine_eq_hasTorusLine,
    hasAnyTorusLine_transform]

theorem outcome_transform (symmetry : TorusSymmetry) (state : State) :
    outcome (transformState symmetry state) = outcome state := by
  unfold outcome transformState
  rw [hasTorusLine_transform, hasTorusLine_transform]

#print axioms reverse_line_geometry
#print axioms hasAnyTorusLine_eq_hasTorusLine
#print axioms lineAt_transform
#print axioms hasTorusLine_transform
#print axioms outcome_transform

end PopTacToe