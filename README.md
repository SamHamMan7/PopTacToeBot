# PopTacToeBot

An experimental high-performance C++ engine and research toolkit for Pop Tac
Toe on an 8x8 board.

The project currently contains a CPU alpha-beta bot, a pure MCTS baseline,
terminal play, paired arenas, live self-play, rule tests, state counting, and
an automated match runner for the published Fairy-Stockfish opponent.

> **Status:** the exact 8x8 Torus ruleset documented below has a formally
> verified Blue forced win. An independent C++ verifier accepted an 879,896-state
> certificate, and the generated Lean replay built successfully through
> `PopTacToe.Generated.Root.initial_blue_forces_win`. The proof only claims
> this exact ruleset; it does not apply to Beginner/Reincarnation or other
> configurations.

## Tested configuration

- 8x8 board with eight checkers per player
- Torus edge wrapping
- Continue when all pieces are on the board
- Travel only when the current player's bin is empty
- King-style travel to an unoccupied adjacent square
- A reincarnated checker must be placed before travel when using a
  reincarnation ruleset
- Pops are applied before checking for three in a row
- Simultaneous winning lines are a draw
- Repeated full positions are draws
- User-facing coordinates are 1 through 8

The general rules engine also contains the Reincarnation, Ringout, Blocked,
Torus, and Klein surfaces plus several movement configurations. The strong
alpha-beta search currently supports Torus + Continue + Move When All On Board
with King movement.

## Build

These commands are intended for an MSYS2 UCRT64 terminal with a current GCC:

```bash
g++ -std=c++20 -O3 -march=native -DNDEBUG -Wall -Wextra -Wpedantic pop_tac_toe_play.cpp -o popplay.exe
g++ -std=c++20 -O3 -march=native -DNDEBUG -Wall -Wextra -Wpedantic pop_tac_toe_arena.cpp -o poparena.exe
g++ -std=c++20 -O3 -march=native -DNDEBUG -Wall -Wextra -Wpedantic watch.cpp -o watch.exe
g++ -std=c++20 -O2 -Wall -Wextra -Wpedantic pop_tac_toe_tests.cpp -o poptests.exe
```

Run the validation suites:

```bash
./popplay.exe selftest
./poparena.exe selftest
./watch.exe selftest
./poptests.exe
```

## Play

Play Red against the alpha-beta bot with three seconds per computer move:

```bash
./popplay.exe red ab:3000
```

Commands inside the game include `p ROW COLUMN`,
`t FROM_ROW FROM_COLUMN TO_ROW TO_COLUMN`, `moves`, `history`, `undo`, and
`quit`.

## Watch self-play

One game, one second of search per move, and a half-second display delay:

```bash
./watch.exe 1 1000 500 0 123456
```

The arguments are `games`, `think-ms`, `display-delay-ms`,
`test-opening-plies`, and `seed`. Set test-opening plies to zero for a normal
empty-board game.

## Arena

Normal paired-color games from the empty board:

```bash
./poparena.exe 20 ab:1000 ab:500 8 512 123456 normal.csv
```

Paired nonterminal six-ply test openings:

```bash
./poparena.exe 20 ab:1000 ab:500 8 512 123456 test.csv 6
```

Test openings are a benchmarking tool, not the normal starting condition. Each
legal opening history is replayed twice with the bots swapping colors so its
color advantage does not count as engine strength.

## Published Fairy-Stockfish opponent

The external opponent is not included in this repository. Install Lucian
Chauvin and McKinley's published package separately:

```bash
npm install poptactoe-fairy-stockfish-nnue.wasm@1.2.1
```

Example equal-time match at the website's maximum settings:

```bash
python match.py --games 20 --bot ab:10000 --fairy-ms 10000 --brains 20 --hash 16 --csv match.csv --log-dir logs
```

The published package contains no Pop Tac Toe NNUE network and reports that it
uses classical evaluation. Its Pop Tac Toe variant does not support selecting
a checker for travel, so the match runner scores only games completed before
that phase. Match results are evidence of playing strength, not a proof of the
game-theoretic result.

## Architecture

- `pop_tac_toe_mcts.cpp`: rules engine and MCTS baseline
- `pop_tac_toe_strong.cpp`: bitboard alpha-beta search
- `pop_tac_toe_play.cpp`: terminal human-versus-bot interface
- `pop_tac_toe_arena.cpp`: paired engine matches and CSV output
- `watch.cpp`: live alpha-beta self-play
- `pop_tac_toe_tests.cpp`: rules and tactical regression tests
- `match.py`: external Fairy-Stockfish match runner

Additional research tools include the proof solver, state counter, strategy
verifier, Lean formalization, and cross-language conformance checks.

## Beginner/Reincarnation research

The Torus theorem does not apply to Beginner/Reincarnation. Experimental work
on that ruleset lives in `pop_tac_toe_beginner_proof.cpp`. It searches only
for a positive finite forced-win certificate and never interprets an exhausted
search as a loss or draw. D4 board symmetries are canonicalized, but colors and
the side to move are preserved.

Build and sanity-check it with:

```bash
g++ -std=c++20 -O3 -march=native -DNDEBUG -Wall -Wextra -Wpedantic pop_tac_toe_beginner_proof.cpp -o beginnerproof.exe
./beginnerproof.exe selftest
```

A first 3-checker search can be run with:

```bash
./beginnerproof.exe blue 3 12 1000000 beginner3-blue.ptc
```

If the result is `PROVEN_WIN`, the emitted certificate is a ranked acyclic
proof DAG. If the result is `UNKNOWN`, no game-theoretic conclusion follows.

## Formal result

For the tested Torus configuration above, Blue can force a terminal win before
travel begins. The independently checked certificate contains 879,896 states.
The full generated Lean replay completed successfully, and `leanchecker`
accepted both `PopTacToe.Generated.Root` and `PopTacToe.Tests`.

The final generated theorem is:

```text
PopTacToe.Generated.Root.initial_blue_forces_win
```

The generated theorem reports only Lean's standard `propext` and
`Quot.sound` axioms, with no `sorryAx`.

Reproduce the full Lean replay from a fresh checkout with:

```bash
rm -rf lean/PopTacToe/Generated
unzip -q certificate/Generated.zip -d lean/PopTacToe
cd lean
lake build
lake env leanchecker PopTacToe.Generated.Root
lake env leanchecker PopTacToe.Tests
```

The certificate metadata is recorded in `certificate/manifest.json`, including
the exact ruleset, state count, Lean version, root theorem, certificate
SHA-256, and SHA-256 of the published generated-replay archive. The generated
Lean modules are stored compactly as `certificate/Generated.zip`. Hosted CI
checks the archive hash, the core Lean project and tests, and a representative
generated chunk; the complete generated-root replay was built and leanchecked
locally because it exceeds the hosted runner's execution window.

## Release

The completed Torus result is published as
[v1.0.0-torus-solution](https://github.com/SamHamMan7/PopTacToeBot/releases/tag/v1.0.0-torus-solution).
The release includes the original `proof.ptc` certificate; its SHA-256 is
`28789eb3b859be0e8999ec224dc946a94b0c3d139d6a577e00e86c52f6573647`.

Further work, such as stronger engines, other rulesets, a DOI archive, or a
research paper, is separate from the completed v1.0 Torus solution.

## Attribution

Pop Tac Toe rules and the browser implementation are available at
[MyMathApps](https://mymathapps.com/mymacalc-sample/MathCircleApps/2PGames/PopTacToe/PopTacToe.html).
The comparison opponent is the separately distributed
[Pop Tac Toe Fairy-Stockfish WASM](https://github.com/lucianchauvin/poptactoe-fairy-stockfish.wasm).

No Fairy-Stockfish binary, WebAssembly file, neural-network file, or
`node_modules` directory should be committed here.

## License

This project is released under the MIT License. See `LICENSE`.
