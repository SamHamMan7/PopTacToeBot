# Formal verification and certificate replay

## Verified theorem

The released result proves one exact Pop Tac Toe ruleset:

```text
board: 8 x 8
checkers: 8 per player
edge: Torus
all on board: Continue
movement: allowed when the current player's bin is empty
movement shape: King
zero-length move: No
jumps: No
win check: after the simultaneous pop
simultaneous Blue and Red lines: Draw
objective: Blue can force a terminal win before travel begins
```

The result applies only to this configuration. It does not establish a winner
for Beginner/Reincarnation, Ringout, Klein, other movement rules, or other
checker counts.

The final Lean theorem is:

```text
PopTacToe.Generated.Root.initial_blue_forces_win
```

The generated theorem reports only Lean's standard `propext` and
`Quot.sound` axioms and no `sorryAx`.

## Computational certificate

The independently checked computational certificate contains 879,896 records.
The original binary certificate is attached to the
[`v1.0.0-torus-solution` release](https://github.com/SamHamMan7/PopTacToeBot/releases/tag/v1.0.0-torus-solution)
as `proof.ptc`.

```text
bytes: 17,597,952
SHA-256: 28789eb3b859be0e8999ec224dc946a94b0c3d139d6a577e00e86c52f6573647
```

The generated Lean replay is published in `certificate/Generated.zip`:

```text
bytes: 7,343,588
SHA-256: 7f267fb98277f3865284996c98be2a051c4e490de5549ac94e875ea8953d3a31
```

The exact machine-readable metadata is in `certificate/manifest.json`.

## Proof architecture

The fast C++ search is used to discover the winning certificate, but the search
program itself is not the trusted basis of the theorem.

The certificate records local winning evidence over the finite placement phase.
At a Blue-to-move state, one certified winning child is enough. At a Red-to-move
state, every legal Red reply must lead to a certified winning child. Terminal
Blue-win states form the base cases.

The placement phase is well-founded under

```text
rank(state) = blueBin(state) + redBin(state)
```

because every placement decreases that rank. The proved strategy reaches a
terminal Blue win before travel begins, so cyclic travel play is outside the
certificate theorem.

Torus symmetries are used to reduce duplicate positions. The Lean development
contains the corresponding geometry, symmetry, canonicalization, transition,
outcome, and force-win equivariance proofs needed to justify that reduction.

Relevant checked Lean modules include:

- `Rules.lean`
- `Geometry.lean`
- `Symmetry.lean`
- `Canonical.lean`
- `Equivariance.lean`
- `PopEquivariance.lean`
- `OutcomeEquivariance.lean`
- `ForceWinEquivariance.lean`
- `PackedRedCertificate.lean`
- `WitnessedCertificate.lean`
- `Tests.lean`

The generated replay is stored separately in `certificate/Generated.zip` and
extracts to `lean/PopTacToe/Generated/`.

## Reproduce the Lean result

The project pins Lean 4.32.0. From a fresh checkout:

```bash
rm -rf lean/PopTacToe/Generated
unzip -q certificate/Generated.zip -d lean/PopTacToe
cd lean
lake build
lake env leanchecker PopTacToe.Generated.Root
lake env leanchecker PopTacToe.Tests
```

These commands completed successfully on the full local replay. The completed
build contained 2149 jobs, including the generated root theorem.

## Hosted CI scope

GitHub Actions intentionally performs a bounded verification pass:

1. extracts `certificate/Generated.zip`;
2. builds the core Lean project;
3. checks `PopTacToe.Tests`;
4. builds a representative generated replay chunk;
5. verifies the manifest constants and generated archive SHA-256.

The full generated-root replay is not rebuilt on the hosted runner because it
exceeds the current runner execution window. The complete root replay was built
and leanchecked locally with the pinned Lean version.

The separate rules workflow also runs the C++ regression suite, browser
JavaScript regression suite, and deterministic C++/browser transition
conformance cases.

## Trust boundary

The final theorem depends on:

- the Lean kernel;
- the checked Lean rule model and soundness proofs;
- the generated proof terms replayed from the certificate.

The C++ solver is not trusted for theorem correctness: a solver error must still
produce data that passes the independent checking and Lean replay layers.

## Release status

The completed result is released as
[`v1.0.0-torus-solution`](https://github.com/SamHamMan7/PopTacToeBot/releases/tag/v1.0.0-torus-solution)
under the MIT License.

Further work such as stronger engines, other Pop Tac Toe rulesets, DOI archival,
or a paper/poster is separate from this completed theorem.
