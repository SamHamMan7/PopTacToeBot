# PopTacToeBot

An experimental high-performance C++ engine and research toolkit for Pop Tac
Toe on an 8x8 board.

The project currently contains a CPU alpha-beta bot, a pure MCTS baseline,
terminal play, paired arenas, live self-play, rule tests, state counting, and
an automated match runner for the published Fairy-Stockfish opponent.

> **Status:** active research. The game has not been solved. The strongest bot
> is optimized for the Torus configuration described below; travel is legal
> and tested but has not yet received the same search optimization as the
> placement phase.

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

Additional research tools may include the proof solver, state counter, and
strategy verifier.

## Current research direction

The immediate goal is to audit forced-win claims from fresh search states. Torus
symmetry reduces Red's replies after the canonical first placement to twelve
unique classes. Solving those classes on demand is more practical than building
a complete table for every position through eight plies.

After that, planned work includes stronger move ordering and search, a
repetition-aware travel transposition table, broader surface support, and only
then policy/value-network experiments.

## Attribution

Pop Tac Toe rules and the browser implementation are available at
[MyMathApps](https://mymathapps.com/mymacalc-sample/MathCircleApps/2PGames/PopTacToe/PopTacToe.html).
The comparison opponent is the separately distributed
[Pop Tac Toe Fairy-Stockfish WASM](https://github.com/lucianchauvin/poptactoe-fairy-stockfish.wasm).

No Fairy-Stockfish binary, WebAssembly file, neural-network file, or
`node_modules` directory should be committed here.

## License

A project license will be selected before the repository is made public. Until
then, the repository remains private.
