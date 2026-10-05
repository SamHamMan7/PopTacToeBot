# Release checklist

The Torus proof result is complete. This checklist tracks the remaining publication work for a stable research release.

## Required before v1.0

- [ ] Choose and add an open-source license.
- [ ] Publish the original `proof.ptc` certificate as a GitHub Release asset.
- [ ] Include the standalone verifier binary or build instructions in the release.
- [ ] Record the certificate SHA-256 in the release notes:
  `28789eb3b859be0e8999ec224dc946a94b0c3d139d6a577e00e86c52f6573647`.
- [ ] Tag the exact release commit, for example `v1.0.0-torus-solution`.
- [ ] Re-run the C++/browser conformance workflow and Lean workflow on the release commit.
- [ ] Confirm the website's solved badge applies only to the exact Torus ruleset.
- [ ] Proofread the README and formal-verification document for stale milestone language.

## Optional archival polish

- [ ] Create a GitHub Release with a short theorem statement and reproduction instructions.
- [ ] Archive the release with Zenodo or another DOI service.
- [ ] Add a short research report or preprint PDF.
- [ ] Add a verification report artifact containing hashes, toolchain version, theorem name, and CI results.

## Exact solved ruleset

- 8x8 board
- 8 checkers per player
- Torus edge wrapping
- Continue after all pieces are placed
- movement allowed when the current player's bin is empty
- King movement
- no zero-length moves
- no jumps
- win checked after simultaneous popping
- simultaneous Blue and Red lines are a draw
- theorem objective: Blue forces a terminal win before travel

Root theorem:

`PopTacToe.Generated.Root.initial_blue_forces_win`
