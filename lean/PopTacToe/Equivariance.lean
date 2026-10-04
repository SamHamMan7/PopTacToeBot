import PopTacToe.Symmetry

namespace PopTacToe

/-- Kernel-computed finite witness for both inverse laws on all 512 maps. -/
def squareBijectionCheck : Bool :=
  allTorusSymmetries.all fun symmetry =>
    (List.finRange 64).all fun square =>
      (transformSquare (inverseSymmetry symmetry)
        (transformSquare symmetry square) == square) &&
      (transformSquare symmetry
        (transformSquare (inverseSymmetry symmetry) square) == square)

theorem all_symmetries_member (symmetry : TorusSymmetry) :
    symmetry ∈ allTorusSymmetries := by
  rcases symmetry with ⟨shape, rowShift, columnShift⟩
  cases shape <;> simp [allTorusSymmetries, d4Values]

theorem square_bijection_check_passes : squareBijectionCheck = true := by
  decide +kernel

/-- `inverseSymmetry` is a left inverse on every square. -/
theorem inverse_transformSquare (symmetry : TorusSymmetry) (square : Square) :
    transformSquare (inverseSymmetry symmetry)
      (transformSquare symmetry square) = square := by
  have checked := square_bijection_check_passes
  simp only [squareBijectionCheck, List.all_eq_true] at checked
  have pair := checked symmetry (all_symmetries_member symmetry)
    square (List.mem_finRange square)
  simp only [Bool.and_eq_true] at pair
  exact eq_of_beq pair.1

/-- `inverseSymmetry` is a right inverse on every square. -/
theorem transformSquare_inverse (symmetry : TorusSymmetry) (square : Square) :
    transformSquare symmetry
      (transformSquare (inverseSymmetry symmetry) square) = square := by
  have checked := square_bijection_check_passes
  simp only [squareBijectionCheck, List.all_eq_true] at checked
  have pair := checked symmetry (all_symmetries_member symmetry)
    square (List.mem_finRange square)
  simp only [Bool.and_eq_true] at pair
  exact eq_of_beq pair.2

theorem transformSquare_injective_iff (symmetry : TorusSymmetry)
    (left right : Square) :
    transformSquare symmetry left = transformSquare symmetry right ↔
      left = right := by
  constructor
  · intro equalImages
    calc
      left = transformSquare (inverseSymmetry symmetry)
          (transformSquare symmetry left) :=
        (inverse_transformSquare symmetry left).symm
      _ = transformSquare (inverseSymmetry symmetry)
          (transformSquare symmetry right) := by rw [equalImages]
      _ = right := inverse_transformSquare symmetry right
  · intro equalSources
    rw [equalSources]

theorem contains_or (left right : Board) (square : Square) :
    contains (left ||| right) square =
      (contains left square || contains right square) := by
  simp [contains]

theorem contains_and (left right : Board) (square : Square) :
    contains (left &&& right) square =
      (contains left square && contains right square) := by
  simp [contains]

theorem contains_xor (left right : Board) (square : Square) :
    contains (left ^^^ right) square =
      Bool.xor (contains left square) (contains right square) := by
  simp [contains]

theorem contains_clearBoard (pieces clear : Board) (square : Square) :
    contains (clearBoard pieces clear) square =
      (contains pieces square && !contains clear square) := by
  unfold clearBoard
  rw [contains_xor, contains_and]
  cases contains pieces square <;> cases contains clear square <;> rfl

theorem contains_zero (square : Square) :
    contains (0 : Board) square = false := by
  exact BitVec.getLsbD_zero

theorem contains_bit (source target : Square) :
    contains (bit source) target = decide (source = target) := by
  unfold contains bit
  rw [show BitVec.ofNat 64 (1 <<< source.val) =
      BitVec.twoPow 64 source.val by rfl]
  simp [Fin.ext_iff, eq_comm]

private theorem contains_transform_fold (symmetry : TorusSymmetry)
    (pieces : Board) (sources : List Square) (accumulator : Board)
    (target : Square) :
    contains
        (sources.foldl (fun transformed source =>
          if contains pieces source then
            transformed ||| bit (transformSquare symmetry source)
          else transformed) accumulator) target =
      (contains accumulator target ||
        sources.any fun source =>
          contains pieces source &&
            decide (transformSquare symmetry source = target)) := by
  induction sources generalizing accumulator with
  | nil => simp
  | cons source rest inductionHypothesis =>
      simp only [List.foldl]
      rw [inductionHypothesis]
      cases occupied : contains pieces source <;>
        simp [occupied, contains_or, contains_bit, Bool.or_assoc]

/-- Exact pointwise semantics of transporting a 64-bit board. -/
theorem contains_transformBoard (symmetry : TorusSymmetry)
    (pieces : Board) (target : Square) :
    contains (transformBoard symmetry pieces) target =
      contains pieces (transformSquare (inverseSymmetry symmetry) target) := by
  rw [transformBoard, contains_transform_fold]
  rw [contains_zero, Bool.false_or]
  change
    ((List.finRange 64).any fun source =>
      contains pieces source &&
        decide (transformSquare symmetry source = target)) =
      contains pieces (transformSquare (inverseSymmetry symmetry) target)
  let inverseTarget := transformSquare (inverseSymmetry symmetry) target
  cases occupied : contains pieces inverseTarget with
  | false =>
      apply (List.any_eq_false).2
      intro source sourceMember evidence
      have parts :
          contains pieces source = true ∧
            decide (transformSquare symmetry source = target) = true := by
        simpa only [Bool.and_eq_true] using evidence
      have image : transformSquare symmetry source = target :=
        of_decide_eq_true parts.2
      have sourceEquals : source = inverseTarget := by
        calc
          source = transformSquare (inverseSymmetry symmetry)
              (transformSquare symmetry source) :=
            (inverse_transformSquare symmetry source).symm
          _ = inverseTarget := by simp [inverseTarget, image]
      rw [sourceEquals] at parts
      simp [occupied] at parts
  | true =>
      apply (List.any_eq_true).2
      refine ⟨inverseTarget, List.mem_finRange inverseTarget, ?_⟩
      simp [occupied, inverseTarget, transformSquare_inverse]

theorem board_eq_of_contains {left right : Board}
    (same : ∀ square : Square, contains left square = contains right square) :
    left = right := by
  apply (BitVec.eq_of_getLsbD_eq_iff).2
  intro index inRange
  exact same ⟨index, inRange⟩

theorem contains_transformBoard_image (symmetry : TorusSymmetry)
    (pieces : Board) (source : Square) :
    contains (transformBoard symmetry pieces)
        (transformSquare symmetry source) = contains pieces source := by
  rw [contains_transformBoard, inverse_transformSquare]

/-- Transport followed by inverse transport recovers every 64-bit board. -/
theorem transformBoard_round_trip (symmetry : TorusSymmetry)
    (pieces : Board) :
    transformBoard (inverseSymmetry symmetry)
      (transformBoard symmetry pieces) = pieces := by
  apply board_eq_of_contains
  intro target
  calc
    contains (transformBoard (inverseSymmetry symmetry)
        (transformBoard symmetry pieces)) target =
      contains (transformBoard (inverseSymmetry symmetry)
        (transformBoard symmetry pieces))
          (transformSquare (inverseSymmetry symmetry)
            (transformSquare symmetry target)) := by
              rw [inverse_transformSquare]
    _ = contains (transformBoard symmetry pieces)
          (transformSquare symmetry target) :=
      contains_transformBoard_image (inverseSymmetry symmetry)
        (transformBoard symmetry pieces) (transformSquare symmetry target)
    _ = contains pieces target :=
      contains_transformBoard_image symmetry pieces target

/-- A spatial permutation distributes over bitboard union. -/
theorem transformBoard_or (symmetry : TorusSymmetry) (left right : Board) :
    transformBoard symmetry (left ||| right) =
      (transformBoard symmetry left ||| transformBoard symmetry right) := by
  apply board_eq_of_contains
  intro target
  rw [contains_transformBoard, contains_or, contains_or,
    contains_transformBoard, contains_transformBoard]

theorem transformBoard_and (symmetry : TorusSymmetry) (left right : Board) :
    transformBoard symmetry (left &&& right) =
      (transformBoard symmetry left &&& transformBoard symmetry right) := by
  apply board_eq_of_contains
  intro target
  rw [contains_transformBoard, contains_and, contains_and,
    contains_transformBoard, contains_transformBoard]

theorem transformBoard_bit (symmetry : TorusSymmetry) (source : Square) :
    transformBoard symmetry (bit source) =
      bit (transformSquare symmetry source) := by
  apply board_eq_of_contains
  intro target
  rw [contains_transformBoard, contains_bit, contains_bit]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · intro sourceEquals
    rw [sourceEquals, transformSquare_inverse]
  · intro imageEquals
    calc
      source = transformSquare (inverseSymmetry symmetry)
          (transformSquare symmetry source) :=
        (inverse_transformSquare symmetry source).symm
      _ = transformSquare (inverseSymmetry symmetry) target := by
        rw [imageEquals]

theorem occupied_transformState (symmetry : TorusSymmetry) (state : State) :
    (transformState symmetry state).occupied =
      transformBoard symmetry state.occupied := by
  simp only [State.occupied, transformState]
  exact (transformBoard_or symmetry state.blue state.red).symm

theorem moverBin_transformState (symmetry : TorusSymmetry) (state : State) :
    (transformState symmetry state).moverBin = state.moverBin := by
  cases state.turn <;> rfl

/-- Legal placement is invariant under every one of the 512 symmetries. -/
theorem legalPlacement_transform (symmetry : TorusSymmetry)
    (state : State) (target : Square) :
    legalPlacement (transformState symmetry state)
        (transformSquare symmetry target) = legalPlacement state target := by
  unfold legalPlacement emptyAt
  rw [moverBin_transformState, occupied_transformState,
    contains_transformBoard, inverse_transformSquare]

#print axioms square_bijection_check_passes
#print axioms inverse_transformSquare
#print axioms transformSquare_inverse
#print axioms contains_transformBoard
#print axioms transformBoard_round_trip
#print axioms transformBoard_or
#print axioms transformBoard_and
#print axioms transformBoard_bit
#print axioms legalPlacement_transform

end PopTacToe