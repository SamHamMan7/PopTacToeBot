# v1.0.0 Torus solution — draft release notes

This release packages the solved 8x8 Torus result for Pop Tac Toe together with
the playable engine, independent certificate tooling, and Lean formalization.

## Result

For the exact ruleset below, Blue has a forced terminal win before travel begins:

- 8x8 board
- 8 checkers per player
- Torus edge wrapping
- Continue after all pieces are placed
- movement when the current player's bin is empty
- King movement
- zero-length moves disabled
- jumps disabled
- win checked after the simultaneous pop
- simultaneous Blue and Red lines are a draw

The Lean root theorem is:

`PopTacToe.Generated.Root.initial_blue_forces_win`

The generated theorem reports only `propext` and `Quot.sound`, with no
`sorryAx`.

## Certificate

The independently checked computational certificate contains 879,896 states.

Original certificate SHA-256:

`28789eb3b859be0e8999ec224dc946a94b0c3d139d6a577e00e86c52f6573647`

The generated Lean replay is published in `certificate/Generated.zip`.

Generated replay archive SHA-256:

`7f267fb98277f3865284996c98be2a051c4e490de5549ac94e875ea8953d3a31`

## Reproduce the Lean result

```bash
rm -rf lean/PopTacToe/Generated
unzip -q certificate/Generated.zip -d lean/PopTacToe
cd lean
lake build
lake env leanchecker PopTacToe.Generated.Root
lake env leanchecker PopTacToe.Tests
```

Lean toolchain: `leanprover/lean4:v4.32.0`.

The complete generated-root replay has been built and checked locally. Hosted
GitHub Actions verifies the archive hash, core Lean project, test module, and a
representative generated certificate chunk because the full replay exceeds the
current hosted runner execution window.

## Conformance

CI also runs the reference C++ rule tests, browser rule tests, and deterministic
cross-language transition cases. The C++ and browser engines must serialize the
same resulting states and outcomes for those shared cases.

## Release assets still to attach

- `proof.ptc`
- optional prebuilt standalone verifier
- optional research report / preprint PDF

Do not publish this draft as the final release until a repository license has
been chosen and the original certificate asset has been attached.
