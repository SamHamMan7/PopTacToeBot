import PopTacToe.Certificate
import PopTacToe.OutcomeEquivariance
import PopTacToe.PopEquivariance

namespace PopTacToe

theorem transformState_round_trip (symmetry : TorusSymmetry) (state : State) :
    transformState (inverseSymmetry symmetry)
      (transformState symmetry state) = state := by
  rcases state with ⟨blue, red, blueBin, redBin, turn⟩
  simp only [transformState]
  rw [transformBoard_round_trip, transformBoard_round_trip]

theorem legalPlacement_transform_iff (symmetry : TorusSymmetry)
    (state : State) (target : Square) :
    LegalPlacement (transformState symmetry state)
        (transformSquare symmetry target) ↔
      LegalPlacement state target := by
  unfold LegalPlacement
  rw [legalPlacement_transform]

theorem blueWins_transform_iff (symmetry : TorusSymmetry) (state : State) :
    BlueWins (transformState symmetry state) ↔ BlueWins state := by
  unfold BlueWins
  rw [outcome_transform]

/-- A spatial symmetry transports a placement-phase forced win. -/
theorem blueForcesWithin_transform_forward (symmetry : TorusSymmetry)
    {fuel : Nat} {state : State}
    (forced : BlueForcesWithin fuel state) :
    BlueForcesWithin fuel (transformState symmetry state) := by
  induction fuel generalizing state with
  | zero =>
      exact (blueWins_transform_iff symmetry state).2 forced
  | succ fuel inductionHypothesis =>
      unfold BlueForcesWithin at forced ⊢
      rcases forced with win | ⟨ongoing, placementPhase, replies⟩
      · exact Or.inl ((blueWins_transform_iff symmetry state).2 win)
      · refine Or.inr ⟨?_, ?_, ?_⟩
        · simpa only [outcome_transform] using ongoing
        · simpa only [moverBin_transformState] using placementPhase
        · change match state.turn with
            | .blue =>
                ∃ target : Square,
                  LegalPlacement (transformState symmetry state) target ∧
                    BlueForcesWithin fuel
                      (applyPlacement (transformState symmetry state) target)
            | .red =>
                ∀ target : Square,
                  LegalPlacement (transformState symmetry state) target →
                    BlueForcesWithin fuel
                      (applyPlacement (transformState symmetry state) target)
          cases turnEquation : state.turn with
          | blue =>
              rw [turnEquation] at replies
              simp only at replies ⊢
              rcases replies with ⟨target, legal, childForced⟩
              refine ⟨transformSquare symmetry target, ?_, ?_⟩
              · exact (legalPlacement_transform_iff symmetry state target).2 legal
              · rw [← applyPlacement_transform]
                exact inductionHypothesis childForced
          | red =>
              rw [turnEquation] at replies
              simp only at replies ⊢
              intro transformedTarget transformedLegal
              let target := transformSquare (inverseSymmetry symmetry)
                transformedTarget
              have returnedLegal :
                  LegalPlacement
                    (transformState (inverseSymmetry symmetry)
                      (transformState symmetry state)) target :=
                (legalPlacement_transform_iff (inverseSymmetry symmetry)
                  (transformState symmetry state) transformedTarget).2
                    transformedLegal
              rw [transformState_round_trip] at returnedLegal
              have childForced := inductionHypothesis
                (replies target returnedLegal)
              rw [applyPlacement_transform, transformSquare_inverse]
                at childForced
              exact childForced

theorem blueForcesWithin_transform_iff (symmetry : TorusSymmetry)
    {fuel : Nat} {state : State} :
    BlueForcesWithin fuel (transformState symmetry state) ↔
      BlueForcesWithin fuel state := by
  constructor
  · intro transformedForced
    have returned := blueForcesWithin_transform_forward
      (inverseSymmetry symmetry) transformedForced
    rw [transformState_round_trip] at returned
    exact returned
  · exact blueForcesWithin_transform_forward symmetry

#print axioms transformState_round_trip
#print axioms blueForcesWithin_transform_iff

end PopTacToe