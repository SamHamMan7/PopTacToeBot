import PopTacToe.Geometry

namespace PopTacToe

theorem contains_clear_fold (blue red : Board) (center : Square)
    (directions : List Direction) (accumulator : Pushes) (target : Square) :
    contains
        ((directions.foldl (collectPush blue red center) accumulator).clear)
        target =
      (contains accumulator.clear target ||
        directions.any fun direction =>
          pushCondition blue red center direction &&
            decide (pushSource center direction = target)) := by
  induction directions generalizing accumulator with
  | nil => simp
  | cons direction rest inductionHypothesis =>
      simp only [List.foldl]
      rw [inductionHypothesis]
      unfold collectPush
      cases allowed : pushCondition blue red center direction <;>
        cases blueSource : contains blue (pushSource center direction) <;>
        simp [allowed, blueSource, contains_or, contains_bit, Bool.or_assoc]

theorem contains_addBlue_fold (blue red : Board) (center : Square)
    (directions : List Direction) (accumulator : Pushes) (target : Square) :
    contains
        ((directions.foldl (collectPush blue red center) accumulator).addBlue)
        target =
      (contains accumulator.addBlue target ||
        directions.any fun direction =>
          pushCondition blue red center direction &&
            contains blue (pushSource center direction) &&
              decide (pushDestination center direction = target)) := by
  induction directions generalizing accumulator with
  | nil => simp
  | cons direction rest inductionHypothesis =>
      simp only [List.foldl]
      rw [inductionHypothesis]
      unfold collectPush
      cases allowed : pushCondition blue red center direction <;>
        cases blueSource : contains blue (pushSource center direction) <;>
        simp [allowed, blueSource, contains_or, contains_bit, Bool.or_assoc]

theorem contains_addRed_fold (blue red : Board) (center : Square)
    (directions : List Direction) (accumulator : Pushes) (target : Square) :
    contains
        ((directions.foldl (collectPush blue red center) accumulator).addRed)
        target =
      (contains accumulator.addRed target ||
        directions.any fun direction =>
          pushCondition blue red center direction &&
            !(contains blue (pushSource center direction)) &&
              decide (pushDestination center direction = target)) := by
  induction directions generalizing accumulator with
  | nil => simp
  | cons direction rest inductionHypothesis =>
      simp only [List.foldl]
      rw [inductionHypothesis]
      unfold collectPush
      cases allowed : pushCondition blue red center direction <;>
        cases blueSource : contains blue (pushSource center direction) <;>
        simp [allowed, blueSource, contains_or, contains_bit, Bool.or_assoc]

def pushClearAt (blue red : Board) (center target : Square) : Bool :=
  pushDirections.any fun direction =>
    pushCondition blue red center direction &&
      decide (pushSource center direction = target)

def pushAddBlueAt (blue red : Board) (center target : Square) : Bool :=
  pushDirections.any fun direction =>
    pushCondition blue red center direction &&
      contains blue (pushSource center direction) &&
        decide (pushDestination center direction = target)

def pushAddRedAt (blue red : Board) (center target : Square) : Bool :=
  pushDirections.any fun direction =>
    pushCondition blue red center direction &&
      !(contains blue (pushSource center direction)) &&
        decide (pushDestination center direction = target)

theorem resolvePops_blue_contains (blue red : Board) (center target : Square) :
    contains (resolvePops blue red center).1 target =
      ((contains blue target && !pushClearAt blue red center target) ||
        pushAddBlueAt blue red center target) := by
  unfold resolvePops pushClearAt pushAddBlueAt
  rw [contains_or, contains_clearBoard,
    contains_clear_fold, contains_addBlue_fold]
  rw [contains_zero]
  simp

theorem resolvePops_red_contains (blue red : Board) (center target : Square) :
    contains (resolvePops blue red center).2 target =
      ((contains red target && !pushClearAt blue red center target) ||
        pushAddRedAt blue red center target) := by
  unfold resolvePops pushClearAt pushAddRedAt
  rw [contains_or, contains_clearBoard,
    contains_clear_fold, contains_addRed_fold]
  rw [contains_zero]
  simp

theorem pushDirections_any_transform (shape : D4)
    (predicate : Direction → Bool) :
    (pushDirections.any fun direction =>
      predicate (transformDirection shape direction)) =
        pushDirections.any predicate := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true]
  constructor
  · rintro ⟨direction, member, accepted⟩
    exact ⟨transformDirection shape direction,
      transformDirection_push_member shape direction member, accepted⟩
  · rintro ⟨direction, member, accepted⟩
    refine ⟨transformDirection (inverseD4 shape) direction,
      transformDirection_push_member (inverseD4 shape) direction member, ?_⟩
    simpa only [transformDirection_inverse] using accepted

theorem pushSource_transform (symmetry : TorusSymmetry)
    (center : Square) (direction : Direction) :
    pushSource (transformSquare symmetry center)
        (transformDirection symmetry.shape direction) =
      transformSquare symmetry (pushSource center direction) := by
  exact (displaced_transform_one symmetry center direction).symm

theorem pushDestination_transform (symmetry : TorusSymmetry)
    (center : Square) (direction : Direction) :
    pushDestination (transformSquare symmetry center)
        (transformDirection symmetry.shape direction) =
      transformSquare symmetry (pushDestination center direction) := by
  exact (displaced_transform_two symmetry center direction).symm

theorem pushCondition_transform (symmetry : TorusSymmetry)
    (blue red : Board) (center : Square) (direction : Direction) :
    pushCondition (transformBoard symmetry blue) (transformBoard symmetry red)
        (transformSquare symmetry center)
        (transformDirection symmetry.shape direction) =
      pushCondition blue red center direction := by
  unfold pushCondition
  rw [pushSource_transform, pushDestination_transform,
    ← transformBoard_or]
  dsimp
  rw [contains_transformBoard_image, contains_transformBoard_image]

theorem pushClearAt_transform (symmetry : TorusSymmetry)
    (blue red : Board) (center target : Square) :
    pushClearAt (transformBoard symmetry blue) (transformBoard symmetry red)
        (transformSquare symmetry center) (transformSquare symmetry target) =
      pushClearAt blue red center target := by
  unfold pushClearAt
  rw [← pushDirections_any_transform symmetry.shape
    (fun direction =>
      pushCondition (transformBoard symmetry blue) (transformBoard symmetry red)
          (transformSquare symmetry center) direction &&
        decide (pushSource (transformSquare symmetry center) direction =
          transformSquare symmetry target))]
  apply congrArg (List.any pushDirections)
  funext direction
  rw [pushCondition_transform, pushSource_transform]
  simp only [transformSquare_injective_iff]

theorem pushAddBlueAt_transform (symmetry : TorusSymmetry)
    (blue red : Board) (center target : Square) :
    pushAddBlueAt (transformBoard symmetry blue) (transformBoard symmetry red)
        (transformSquare symmetry center) (transformSquare symmetry target) =
      pushAddBlueAt blue red center target := by
  unfold pushAddBlueAt
  rw [← pushDirections_any_transform symmetry.shape
    (fun direction =>
      pushCondition (transformBoard symmetry blue) (transformBoard symmetry red)
          (transformSquare symmetry center) direction &&
        contains (transformBoard symmetry blue)
          (pushSource (transformSquare symmetry center) direction) &&
        decide (pushDestination (transformSquare symmetry center) direction =
          transformSquare symmetry target))]
  apply congrArg (List.any pushDirections)
  funext direction
  rw [pushCondition_transform, pushSource_transform,
    pushDestination_transform, contains_transformBoard_image]
  simp only [transformSquare_injective_iff]

theorem pushAddRedAt_transform (symmetry : TorusSymmetry)
    (blue red : Board) (center target : Square) :
    pushAddRedAt (transformBoard symmetry blue) (transformBoard symmetry red)
        (transformSquare symmetry center) (transformSquare symmetry target) =
      pushAddRedAt blue red center target := by
  unfold pushAddRedAt
  rw [← pushDirections_any_transform symmetry.shape
    (fun direction =>
      pushCondition (transformBoard symmetry blue) (transformBoard symmetry red)
          (transformSquare symmetry center) direction &&
        !(contains (transformBoard symmetry blue)
          (pushSource (transformSquare symmetry center) direction)) &&
        decide (pushDestination (transformSquare symmetry center) direction =
          transformSquare symmetry target))]
  apply congrArg (List.any pushDirections)
  funext direction
  rw [pushCondition_transform, pushSource_transform,
    pushDestination_transform, contains_transformBoard_image]
  simp only [transformSquare_injective_iff]

theorem board_eq_of_contains_images (symmetry : TorusSymmetry)
    {left right : Board}
    (same : ∀ source : Square,
      contains left (transformSquare symmetry source) =
        contains right (transformSquare symmetry source)) :
    left = right := by
  apply board_eq_of_contains
  intro target
  let source := transformSquare (inverseSymmetry symmetry) target
  calc
    contains left target =
        contains left (transformSquare symmetry source) := by
      rw [transformSquare_inverse]
    _ = contains right (transformSquare symmetry source) := same source
    _ = contains right target := by rw [transformSquare_inverse]

theorem resolvePops_transform (symmetry : TorusSymmetry)
    (blue red : Board) (center : Square) :
    resolvePops (transformBoard symmetry blue) (transformBoard symmetry red)
        (transformSquare symmetry center) =
      (transformBoard symmetry (resolvePops blue red center).1,
        transformBoard symmetry (resolvePops blue red center).2) := by
  apply Prod.ext
  · apply board_eq_of_contains_images symmetry
    intro target
    change contains
        (resolvePops (transformBoard symmetry blue) (transformBoard symmetry red)
          (transformSquare symmetry center)).1
        (transformSquare symmetry target) =
      contains (transformBoard symmetry (resolvePops blue red center).1)
        (transformSquare symmetry target)
    rw [resolvePops_blue_contains]
    rw [contains_transformBoard_image, pushClearAt_transform,
      pushAddBlueAt_transform]
    rw [contains_transformBoard_image, resolvePops_blue_contains]
  · apply board_eq_of_contains_images symmetry
    intro target
    change contains
        (resolvePops (transformBoard symmetry blue) (transformBoard symmetry red)
          (transformSquare symmetry center)).2
        (transformSquare symmetry target) =
      contains (transformBoard symmetry (resolvePops blue red center).2)
        (transformSquare symmetry target)
    rw [resolvePops_red_contains]
    rw [contains_transformBoard_image, pushClearAt_transform,
      pushAddRedAt_transform]
    rw [contains_transformBoard_image, resolvePops_red_contains]

theorem applyPlacement_transform (symmetry : TorusSymmetry)
    (state : State) (target : Square) :
    transformState symmetry (applyPlacement state target) =
      applyPlacement (transformState symmetry state)
        (transformSquare symmetry target) := by
  rcases state with ⟨blue, red, blueBin, redBin, turn⟩
  cases turn <;> simp only [applyPlacement, transformState]
  · rw [← transformBoard_bit, ← transformBoard_or,
      resolvePops_transform]
  · rw [← transformBoard_bit, ← transformBoard_or,
      resolvePops_transform]

#print axioms resolvePops_blue_contains
#print axioms pushCondition_transform
#print axioms resolvePops_transform
#print axioms applyPlacement_transform

end PopTacToe