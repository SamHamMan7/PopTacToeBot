import PopTacToe.Milestone

namespace PopTacToe

def adjacentPushState : State := {
  red := boardOf [cell 3 4]
  redBin := 7
}

theorem adjacent_piece_moves_away :
    let child := applyPlacement adjacentPushState (cell 3 3)
    contains child.red (cell 3 4) = false ∧
      contains child.red (cell 3 5) = true := by
  decide +kernel

def blockedPushState : State := {
  blue := boardOf [cell 3 5]
  red := boardOf [cell 3 4]
  blueBin := 7
  redBin := 7
}

theorem checker_behind_blocks_push :
    let child := applyPlacement blockedPushState (cell 3 3)
    contains child.red (cell 3 4) = true := by
  decide +kernel

def eightSources : List Square :=
  pushDirections.map fun direction => displaced (cell 3 3) direction 1

def eightDestinations : List Square :=
  pushDirections.map fun direction => displaced (cell 3 3) direction 2

def simultaneousPushState : State := {
  red := boardOf eightSources
  redBin := 0
}

theorem all_eight_pushes_are_simultaneous :
    let child := applyPlacement simultaneousPushState (cell 3 3)
    (∀ source ∈ eightSources, contains child.red source = false) ∧
      (∀ destination ∈ eightDestinations,
        contains child.red destination = true) := by
  decide +kernel

def torusPushState : State := {
  red := boardOf [cell 3 0]
  redBin := 7
}

theorem push_wraps_across_torus_edge :
    let child := applyPlacement torusPushState (cell 3 7)
    contains child.red (cell 3 0) = false ∧
      contains child.red (cell 3 1) = true := by
  decide +kernel

def temporaryLineState : State := {
  blue := boardOf [cell 3 2, cell 3 4]
  blueBin := 6
}

theorem win_is_checked_after_pop :
    outcome (applyPlacement temporaryLineState (cell 3 3)) = .ongoing := by
  decide +kernel

def wrappedLineState : State := {
  blue := boardOf [cell 0 7, cell 0 0, cell 0 1]
  blueBin := 5
}

theorem torus_winning_line_wraps :
    outcome wrappedLineState = .blueWin := by
  decide +kernel

def simultaneousLinesState : State := {
  blue := boardOf [cell 0 7, cell 0 0, cell 0 1]
  red := boardOf [cell 3 2, cell 4 2, cell 5 2]
  blueBin := 5
  redBin := 5
}

theorem simultaneous_lines_are_draw :
    outcome simultaneousLinesState = .draw := by
  decide +kernel

#print axioms adjacent_piece_moves_away
#print axioms all_eight_pushes_are_simultaneous
#print axioms win_is_checked_after_pop
#print axioms simultaneous_lines_are_draw

end PopTacToe
