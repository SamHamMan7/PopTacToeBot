import PopTacToe.ForceWinEquivariance

namespace PopTacToe

def State.moverBoard (state : State) : Board :=
  match state.turn with
  | .blue => state.blue
  | .red => state.red

def State.opponentBoard (state : State) : Board :=
  match state.turn with
  | .blue => state.red
  | .red => state.blue

/-- The exact lexicographic preference used by the C++ certificate verifier. -/
def canonicalBetter (candidate current : State) : Bool :=
  if candidate.occupied.toNat = current.occupied.toNat then
    if candidate.moverBoard.toNat = current.moverBoard.toNat then
      decide (candidate.opponentBoard.toNat > current.opponentBoard.toNat)
    else
      decide (candidate.moverBoard.toNat > current.moverBoard.toNat)
  else
    decide (candidate.occupied.toNat > current.occupied.toNat)

def canonicalChoice (candidate current : State) : State :=
  if canonicalBetter candidate current then candidate else current

def canonicalCandidates (state : State) : List State :=
  allTorusSymmetries.map fun symmetry => transformState symmetry state

/-- Select the C++ verifier's maximal representative of a torus orbit. -/
def canonicalState (state : State) : State :=
  (canonicalCandidates state).foldr canonicalChoice state

theorem foldCanonicalChoice_eq_base_or_mem (base : State) :
    ∀ candidates : List State,
      candidates.foldr canonicalChoice base = base ∨
        candidates.foldr canonicalChoice base ∈ candidates := by
  intro candidates
  induction candidates with
  | nil => exact Or.inl rfl
  | cons candidate rest inductionHypothesis =>
      simp only [List.foldr]
      cases betterEquation : canonicalBetter candidate
          (rest.foldr canonicalChoice base) with
      | false =>
          simp only [canonicalChoice, betterEquation, Bool.false_eq_true, if_false]
          rcases inductionHypothesis with equalsBase | inRest
          · exact Or.inl equalsBase
          · exact Or.inr (List.mem_cons_of_mem candidate inRest)
      | true =>
          simp only [canonicalChoice, betterEquation, if_true]
          exact Or.inr (List.mem_cons_self)

theorem canonicalState_eq_self_or_transform (state : State) :
    canonicalState state = state ∨
      ∃ symmetry ∈ allTorusSymmetries,
        canonicalState state = transformState symmetry state := by
  have selected := foldCanonicalChoice_eq_base_or_mem state
    (canonicalCandidates state)
  rcases selected with equalsSelf | inCandidates
  · exact Or.inl equalsSelf
  · right
    rcases List.mem_map.mp inCandidates with
      ⟨symmetry, symmetryMember, transformedEquals⟩
    exact ⟨symmetry, symmetryMember, transformedEquals.symm⟩

theorem outcome_canonicalState (state : State) :
    outcome (canonicalState state) = outcome state := by
  rcases canonicalState_eq_self_or_transform state with
    equalsSelf | ⟨symmetry, _, equalsTransform⟩
  · rw [equalsSelf]
  · rw [equalsTransform, outcome_transform]

theorem blueForcesWithin_canonical_iff {fuel : Nat} {state : State} :
    BlueForcesWithin fuel (canonicalState state) ↔
      BlueForcesWithin fuel state := by
  rcases canonicalState_eq_self_or_transform state with
    equalsSelf | ⟨symmetry, _, equalsTransform⟩
  · rw [equalsSelf]
  · rw [equalsTransform]
    exact blueForcesWithin_transform_iff symmetry

#print axioms outcome_canonicalState
#print axioms blueForcesWithin_canonical_iff

end PopTacToe