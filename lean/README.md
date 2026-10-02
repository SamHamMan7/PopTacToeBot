# Pop Tac Toe Lean verification

This dependency-free Lean 4 project formalizes the placement phase of the
solved ruleset:

- 8x8 board and 8 checkers per player
- Torus edges
- Simultaneous eight-direction pops
- Win checked after the pop
- Wrapped three-in-a-row lines
- Simultaneous Blue and Red lines are a draw
- Ongoing travel-boundary states are not treated as placement-phase wins

It proves the rule and certificate soundness infrastructure used by the full
generated replay. On the completed local proof tree, Lean also accepted:

```text
PopTacToe.Generated.Root.initial_blue_forces_win
```

The replay covers the independently verified 879,896-state certificate and
establishes that Blue can force a terminal win before travel begins.

The milestone uses `decide +kernel`. It contains no `sorry`, `native_decide`,
`Lean.ofReduceBool`, or compiler-trust axiom. `#print axioms` reports only
Lean's standard `propext` and `Quot.sound` axioms.

## Check it

Install Lean 4 through Elan or the official VS Code Lean extension, then run:

```bash
cd lean
lake build
lake env leanchecker PopTacToe.Tests
```

The pinned version is Lean 4.32.0 and no external package is downloaded.

## Full replay status

The full generated replay has been run successfully on Lean 4.32.0. The final
checks used were:

```bash
lake build
lake env leanchecker PopTacToe.Generated.Root
lake env leanchecker PopTacToe.Tests
```

The build completed all 2149 jobs, including the root theorem. The generated
root theorem depends only on Lean's standard `propext` and `Quot.sound`
axioms.

The large generated replay modules are still local and have not yet been
committed here. Until they are published, this repository contains the
formalization milestone but not the complete reproducible 879,896-state replay.
