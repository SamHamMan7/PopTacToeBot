import PopTacToe.Canonical

namespace PopTacToe

/-- Check a record against a set keyed by canonical state representatives. -/
def canonicalLocalCheck (known : State → Bool)
    (entry : CertificateEntry) : Bool :=
  localCheck (fun state => known (canonicalState state)) entry

theorem canonicalLocalCheck_sound {fuel : Nat} {known : State → Bool}
    {entry : CertificateEntry}
    (checked : canonicalLocalCheck known entry = true)
    (knownSound : ∀ state, known state = true →
      BlueForcesWithin fuel state) :
    BlueForcesWithin (fuel + 1) entry.state := by
  apply localCheck_sound (by simpa [canonicalLocalCheck] using checked)
  intro state stateKnown
  exact blueForcesWithin_canonical_iff.mp
    (knownSound (canonicalState state) stateKnown)

/-- Record 1766 (zero-based) from the version-1 `proof.ptc` artifact. -/
def rank2CertificateFixture : CertificateEntry := {
  state := {
    blue := BitVec.ofNat 64 88047521792
    red := BitVec.ofNat 64 14989105464092917762
    blueBin := 1
    redBin := 1
    turn := .blue
  }
  blueChoice := some (Fin.ofNat 64 8)
}

def noCanonicalStates (_ : State) : Bool := false

theorem rank2_fixture_is_canonical :
    canonicalState rank2CertificateFixture.state =
      rank2CertificateFixture.state := by
  decide +kernel

theorem rank2_fixture_checked :
    canonicalLocalCheck noCanonicalStates rank2CertificateFixture = true := by
  decide +kernel

theorem rank2_fixture_forces_blue_win :
    BlueForcesWithin 1 rank2CertificateFixture.state := by
  apply canonicalLocalCheck_sound (fuel := 0) rank2_fixture_checked
  intro state impossible
  simp [noCanonicalStates] at impossible

#print axioms canonicalLocalCheck_sound
#print axioms rank2_fixture_is_canonical
#print axioms rank2_fixture_forces_blue_win

end PopTacToe