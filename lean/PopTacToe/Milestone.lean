import PopTacToe.Certificate

namespace PopTacToe

/-- A legal eight-ply prefix copied from the independently verified game log. -/
def samplePrefix : List Square := [
  cell 0 0,
  cell 1 1,
  cell 5 7,
  cell 1 7,
  cell 0 7,
  cell 6 0,
  cell 1 7,
  cell 0 0
]

def sampleState : State := {
  blue := boardOf [cell 2 6, cell 4 6, cell 6 6, cell 7 7]
  red := boardOf [cell 0 0, cell 2 2, cell 3 7, cell 6 0]
  blueBin := 4
  redBin := 4
  turn := .blue
}

theorem samplePrefix_reaches_state :
    playPlacements? initial samplePrefix = some sampleState := by
  decide +kernel

def sampleEntry : CertificateEntry := {
  state := sampleState
  blueChoice := some (cell 5 5)
}

def noKnownStates (_ : State) : Bool := false

theorem sampleEntry_checked :
    localCheck noKnownStates sampleEntry = true := by
  decide +kernel

theorem sampleEntry_forces_blue_win :
    BlueForcesWithin 1 sampleState := by
  apply localCheck_sound (fuel := 0) sampleEntry_checked
  intro state impossible
  simp [noKnownStates] at impossible

theorem reachable_sample_has_verified_win :
    ∃ state,
      playPlacements? initial samplePrefix = some state ∧
        BlueForcesWithin 1 state := by
  exact ⟨sampleState, samplePrefix_reaches_state,
    sampleEntry_forces_blue_win⟩

#print axioms remaining_applyPlacement
#print axioms localCheck_sound
#print axioms reachable_sample_has_verified_win

end PopTacToe
