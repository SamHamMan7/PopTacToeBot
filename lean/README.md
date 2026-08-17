# Pop Tac Toe Lean milestone

This dependency-free Lean 4 project formalizes the placement phase of the
solved ruleset:

- 8x8 board and 8 checkers per player
- Torus edges
- Simultaneous eight-direction pops
- Win checked after the pop
- Wrapped three-in-a-row lines
- Simultaneous Blue and Red lines are a draw
- Ongoing travel-boundary states are not treated as placement-phase wins

It proves:

1. A legal placement reduces the remaining-bin rank by exactly one.
2. The local certificate checker is sound with respect to the recursive game
   semantics: one certified move is required at a Blue node and every legal
   move is required at a Red node.
3. A real legal eight-ply prefix reaches a position whose one-record
   certificate proves a Blue win on the next placement.

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

## Scope

This is the small, kernel-checked milestone. It does not yet import the
879,896-state `proof.ptc`. The next stage is a rank-chunked certificate format
and a formally proved bridge for canonical torus symmetries, followed by the
full certificate replay.
