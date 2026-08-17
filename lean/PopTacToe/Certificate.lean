import PopTacToe.Rules

namespace PopTacToe

/--
`BlueForcesWithin fuel state` is the placement-phase game semantics used by
the certificate. Terminal Blue wins are accepted immediately. Otherwise Blue
must provide one winning placement, while every legal Red placement must keep
the proposition true. An ongoing travel-boundary state is deliberately false.
-/
def BlueForcesWithin : Nat → State → Prop
  | 0, state => BlueWins state
  | fuel + 1, state =>
      BlueWins state ∨
        (outcome state = .ongoing ∧ 0 < state.moverBin ∧
          match state.turn with
          | .blue =>
              ∃ target : Square,
                LegalPlacement state target ∧
                  BlueForcesWithin fuel (applyPlacement state target)
          | .red =>
              ∀ target : Square,
                LegalPlacement state target →
                  BlueForcesWithin fuel (applyPlacement state target))

theorem blueWins_forcesWithin (fuel : Nat) {state : State}
    (win : BlueWins state) : BlueForcesWithin fuel state := by
  cases fuel with
  | zero => exact win
  | succ fuel => exact Or.inl win

structure CertificateEntry where
  state : State
  blueChoice : Option Square
  deriving BEq, DecidableEq, Repr

/--
One certificate record is locally valid relative to a set of already-proven
states. Blue records contain one existential move. Red records contain no move
and must cover every legal placement.
-/
def LocalCertificate (known : State → Prop)
    (entry : CertificateEntry) : Prop :=
  outcome entry.state = .ongoing ∧ 0 < entry.state.moverBin ∧
    match entry.state.turn with
    | .blue =>
        ∃ target : Square,
          entry.blueChoice = some target ∧
            LegalPlacement entry.state target ∧
              (BlueWins (applyPlacement entry.state target) ∨
                known (applyPlacement entry.state target))
    | .red =>
        entry.blueChoice = none ∧
          ∀ target : Square,
            LegalPlacement entry.state target →
              (BlueWins (applyPlacement entry.state target) ∨
                known (applyPlacement entry.state target))

instance (known : State → Prop) [DecidablePred known]
    (entry : CertificateEntry) : Decidable (LocalCertificate known entry) := by
  rcases entry with ⟨⟨blue, red, blueBin, redBin, turn⟩, choice⟩
  cases turn <;> unfold LocalCertificate <;> dsimp <;> infer_instance

def localCheck (known : State → Bool) (entry : CertificateEntry) : Bool :=
  decide (LocalCertificate (fun state => known state = true) entry)

theorem localCertificate_sound {fuel : Nat} {known : State → Prop}
    {entry : CertificateEntry}
    (valid : LocalCertificate known entry)
    (knownSound : ∀ state, known state → BlueForcesWithin fuel state) :
    BlueForcesWithin (fuel + 1) entry.state := by
  rcases entry with ⟨⟨blue, red, blueBin, redBin, turn⟩, choice⟩
  cases turn with
  | blue =>
      rcases valid with
        ⟨ongoing, placementPhase, target, choiceEq, legal, child⟩
      refine Or.inr ⟨ongoing, placementPhase, ?_⟩
      refine ⟨target, legal, ?_⟩
      cases child with
      | inl win => exact blueWins_forcesWithin fuel win
      | inr found => exact knownSound _ found
  | red =>
      rcases valid with
        ⟨ongoing, placementPhase, choiceEq, children⟩
      refine Or.inr ⟨ongoing, placementPhase, ?_⟩
      intro target legal
      cases children target legal with
      | inl win => exact blueWins_forcesWithin fuel win
      | inr found => exact knownSound _ found

theorem localCheck_sound {fuel : Nat} {known : State → Bool}
    {entry : CertificateEntry}
    (checked : localCheck known entry = true)
    (knownSound : ∀ state, known state = true →
      BlueForcesWithin fuel state) :
    BlueForcesWithin (fuel + 1) entry.state := by
  apply localCertificate_sound
  · exact of_decide_eq_true (by simpa [localCheck] using checked)
  · exact knownSound

end PopTacToe
