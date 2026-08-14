# Formal verification and certificate plan

## What is being proved

The proof must name one exact ruleset. The current solver target is:

```text
board: 8 × 8
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

The website may offer many other rule combinations, but those combinations must not inherit the proof badge. A theorem about the Torus solver configuration is not a theorem about Reincarnation, Ringout, Klein, Queen movement, or another checker count.

## The roles of the programs

### C++ solver

The solver is allowed to be complicated and fast. It searches the game graph, uses bitboards, symmetry, transposition tables, and move ordering, and emits a certificate.

The solver is **not trusted** for the final theorem. A bug in the solver should make the certificate fail verification rather than create a false proof.

### Certificate

The certificate is data. It records enough local evidence to reconstruct the force-win argument without rerunning the expensive search.

For a proof that Blue can force a win before travel:

- A terminal Blue-win state is a base case.
- At a Blue-to-move state, the certificate supplies one legal move to a certified winning child.
- At a Red-to-move state, every legal Red reply must lead to a certified winning child.
- Symmetric children may be represented by one canonical state, provided Lean proves that canonicalization preserves legal transitions and outcomes.

The placement phase is especially convenient because every placement decreases

```text
rank(state) = blueBin(state) + redBin(state)
```

by one. This makes the proof graph well-founded until both bins are empty. The current objective stops at that boundary, so travel cycles do not have to be included in this theorem.

### Lean model and checker

Lean contains a small, readable model of the rules plus a Boolean checker. It proves once that checker acceptance implies the mathematical force-win property. Lean then checks the generated certificate data.

### Lean kernel

The kernel checks the final proof term. The audit command is:

```text
#print axioms PopTacToe.initial_blue_forces_win_before_travel
```

A finished kernel-only result should not contain `sorryAx`, a project-specific assumption, or a native-computation axiom. Standard `propext` and `Quot.sound` may remain, depending on library lemmas used by the development.

## Recommended repository structure

```text
lean/
  lean-toolchain
  lakefile.toml
  PopTacToe/
    Basic.lean
    Rules.lean
    Transition.lean
    Outcome.lean
    Reachable.lean
    Symmetry.lean
    Canonical.lean
    ForceWin.lean
    CertificateFormat.lean
    CertificateChecker.lean
    CertificateSoundness.lean
    Generated/
      Manifest.lean
      Rank00/
      Rank01/
      ...
      Rank16/
    FullCertificate.lean
    Tests.lean
certificate/
  manifest.json
  rank-00/
  rank-01/
  ...
  rank-16/
```

The generated Lean modules should be reproducible outputs of a certificate-conversion tool. Do not edit them by hand.

## Core Lean definitions

Illustrative declarations follow. The exact names should match the existing milestone.

```lean
namespace PopTacToe

abbrev Square := Fin 64

inductive Player
  | blue
  | red
  deriving DecidableEq, Repr

structure State where
  blue       : BitVec 64
  red        : BitVec 64
  blueBin    : Fin 9
  redBin     : Fin 9
  sideToMove : Player
  deriving DecidableEq, Repr

inductive Move
  | place (to : Square)
  | travel (from to : Square)
  deriving DecidableEq, Repr

inductive Outcome
  | ongoing
  | blueWin
  | redWin
  | draw
  deriving DecidableEq, Repr

end PopTacToe
```

Use one executable transition definition as the source of truth:

```lean
def applyMove? (s : State) (m : Move) : Option State := ...
```

Then define legality through it, or prove that a separate legal-move generator agrees with it.

## Force-win predicate for the finite placement objective

A proof-friendly relation can mirror the AND/OR graph:

```lean
inductive BlueForcesWinBeforeTravel : State → Prop
  | terminal
      (h : outcome s = .blueWin) :
      BlueForcesWinBeforeTravel s

  | blueChoice
      (hTurn : s.sideToMove = .blue)
      (hOngoing : outcome s = .ongoing)
      (m : Move)
      (child : State)
      (hApply : applyMove? s m = some child)
      (hChild : BlueForcesWinBeforeTravel child) :
      BlueForcesWinBeforeTravel s

  | redAll
      (hTurn : s.sideToMove = .red)
      (hOngoing : outcome s = .ongoing)
      (hAll : ∀ m child,
        applyMove? s m = some child →
        BlueForcesWinBeforeTravel child) :
      BlueForcesWinBeforeTravel s
```

In practice, the theorem may use rank-indexed predicates or finite maps so that Lean can assemble proofs efficiently.

## Certificate entry design

A compact logical entry can be modeled as:

```lean
structure StateKey where
  blue       : UInt64
  red        : UInt64
  blueBin    : UInt8
  redBin     : UInt8
  sideToMove : Player
  deriving DecidableEq, Repr

inductive Witness
  | terminalBlueWin
  | blueMove (move : EncodedMove) (child : StateKey)
  | redReplies (children : Array StateKey)
  deriving Repr

structure Entry where
  key     : StateKey
  witness : Witness
  deriving Repr
```

For a Red node, the checker should regenerate all legal moves itself, canonicalize their children, remove duplicates in a proved-safe way, and compare that complete set with the referenced child keys. The certificate must not be allowed to omit an inconvenient Red reply.

## Local checker

```lean
def localCheck
    (alreadyVerified : StateKey → Bool)
    (entry : Entry) : Bool :=
  match decode entry.key, entry.witness with
  | some s, .terminalBlueWin =>
      outcome s == .blueWin
  | some s, .blueMove encoded childKey =>
      s.sideToMove == .blue &&
      match decodeMove encoded, decode childKey with
      | some m, some child =>
          applyMove? s m == some child &&
          canonicalKey child == childKey &&
          alreadyVerified childKey
      | _, _ => false
  | some s, .redReplies childKeys =>
      s.sideToMove == .red &&
      canonicalChildren s == childKeys &&
      childKeys.all alreadyVerified
  | _, _ => false
```

The essential theorem is generic:

```lean
theorem localCheck_sound
    (hPrevious : ∀ key, alreadyVerified key = true →
      BlueForcesWinBeforeTravel (decodeState key))
    (hCheck : localCheck alreadyVerified entry = true) :
    BlueForcesWinBeforeTravel (decodeState entry.key) := by
  ...
```

This theorem is the trust bridge. It must be proved manually from the definitions, not assumed for the generated certificate.

## Symmetry milestone

The Torus placement search uses 512 spatial maps: eight square symmetries combined with 64 row/column translations. Lean should define the same transformations and prove:

```lean
theorem transform_applyMove
    (g : TorusSymmetry) :
    applyMove? (transformState g s) (transformMove g m) =
      Option.map (transformState g) (applyMove? s m) := by
  ...

theorem transform_outcome
    (g : TorusSymmetry) :
    outcome (transformState g s) = outcome s := by
  ...

theorem canonicalKey_invariant
    (g : TorusSymmetry) :
    canonicalKey (transformState g s) = canonicalKey s := by
  ...
```

Do not merely reimplement the C++ canonicalizer and test it. The theorem must connect transformed legal moves and outcomes.

## Chunking the 879,896-state certificate

A practical layout is:

```text
rank 0  : boundary/terminal entries
rank 1  : references only rank 0
rank 2  : references only rank 1 or lower
...
rank 16 : contains the initial state
```

Split each rank into deterministic chunks, for example 2,000–10,000 entries per generated module. Each chunk exports a theorem that its keys are verified assuming the lower-rank map.

```lean
theorem rank07_chunk003_sound :
    VerifiedMap rank07Chunk003 := by
  exact verifyChunk_sound lowerRanks rank07Chunk003 (by decide)
```

For a certificate this large, one enormous `by decide` is likely to be slow and memory-hungry. Prefer generated proof terms or small reducible checks whose results are combined by ordinary theorems. Measure chunk size on the pinned Lean version.

## Pure-kernel versus native checking

There are two different products:

1. **Fast Lean executable verification** — compile a Lean checker and run it over the binary certificate. This is valuable independent validation, but an IO program printing `PASS` is not itself a theorem.
2. **Kernel theorem** — elaborate proof terms showing that the initial state satisfies the force-win predicate.

Native evaluation is fast, but it introduces a native-computation assumption for the asserted result. If the goal is validation by `leanchecker` with only the normal logical axioms, use kernel-reducible proofs or generated proof terms rather than `native_decide`.

## Manifest and reproducibility

Publish a manifest beside the certificate:

```json
{
  "format": "poptactoe-certificate-v1",
  "ruleset": "torus-continue-all-on-board-king-8-v1",
  "objective": "blue-forced-terminal-win-before-travel",
  "stateCount": 879896,
  "solverCommit": "<git commit>",
  "converterCommit": "<git commit>",
  "leanToolchain": "leanprover/lean4:v4.32.0",
  "certificateSha256": "<sha256>",
  "rootKey": "<canonical initial state>",
  "chunks": [
    {"rank": 0, "path": "rank-00/chunk-000.ptc", "sha256": "..."}
  ]
}
```

The verifier should reject a mismatched format version, ruleset ID, checker count, state count, root key, or chunk hash.

## Cross-language conformance

A Lean theorem proves facts about the Lean model. To justify that the website and C++ engine implement that model, add shared transition vectors:

```text
input state + move
expected legal/illegal result
expected child state
expected pushed pieces
expected outcome
```

Generate thousands of deterministic cases and run them through:

- the reference C++ `GameState`
- the optimized C++ bitboard engine
- the JavaScript browser engine
- a Lean evaluator or exported Lean test data

This does not replace the theorem, but it catches encoding drift between products.

## CI without normal terminal use

After the Lean sources and generated certificate modules are committed, GitHub Actions can run the verification on every relevant change:

```text
lake build
lake env leanchecker PopTacToe.FullCertificate
```

The workflow should also:

- verify every manifest hash
- regenerate a small fixture and compare it byte-for-byte
- run C++ and JavaScript rule tests
- print the axioms of the final theorem
- upload a verification report as an artifact

Normal users then only open the website. Terminal commands remain developer and CI operations, not part of playing the game.

## Immediate next milestones

1. Merge the browser prototype and deploy it as a static site.
2. Commit the existing `lean/` milestone to this repository.
3. Add `Symmetry.lean` and prove transition/outcome preservation.
4. Freeze and document the existing certificate format and SHA-256.
5. Write a converter that emits a tiny generated Lean chunk.
6. Prove the tiny chunk through the generic soundness theorem.
7. Tune chunk size, then generate and check all 879,896 entries.
8. Export the final root theorem and verification manifest.
