#!/usr/bin/env python3
"""Automated match against Lucian and McKinley's Fairy-Stockfish bot.

Install the published opponent first:
    npm install poptactoe-fairy-stockfish-nnue.wasm@1.2.1

Then compile pop_tac_toe_play.cpp and run, for example:
    python pop_tac_toe_fairy_match.py --games 20 --bot ab:1000 --fairy-ms 1000

Colors and random seeds are paired, every transcript is retained, and a CSV
summary is written for later analysis. The published opponent cannot select a
source checker for King travel. A game that reaches that phase is therefore
marked unsupported instead of being counted as a win, loss, or draw. Completed
games are exact under Torus + Continue + Move When All On Board + King rules.
"""

from __future__ import annotations

import argparse
import csv
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time


PACKAGE_NAME = "poptactoe-fairy-stockfish-nnue.wasm"
PACKAGE_VERSION = "1.2.1"
RULES = "torus+continue+move_when_all_on_board+king"


def executable(name: str) -> str:
    resolved = shutil.which(name)
    if resolved is None:
        raise RuntimeError(f"Required executable not found on PATH: {name}")
    return resolved


def resolve_fairy_uci(explicit: str | None, npm: str) -> Path:
    if explicit is not None:
        path = Path(explicit).expanduser().resolve()
        if not path.is_file():
            raise RuntimeError(f"Fairy UCI wrapper does not exist: {path}")
        return path

    local = Path.cwd() / "node_modules" / PACKAGE_NAME / "uci.js"
    if local.is_file():
        return local.resolve()

    try:
        npm_root = subprocess.run(
            [npm, "root"],
            check=True,
            capture_output=True,
            text=True,
        ).stdout.strip()
    except subprocess.CalledProcessError as error:
        raise RuntimeError("Could not query npm's package directory") from error
    candidate = Path(npm_root) / PACKAGE_NAME / "uci.js"
    if candidate.is_file():
        return candidate.resolve()

    raise RuntimeError(
        f"Published opponent is not installed. Run:\n"
        f"  npm install {PACKAGE_NAME}@{PACKAGE_VERSION}"
    )


class FairyEngine:
    def __init__(
        self,
        node: str,
        uci_path: Path,
        hash_megabytes: int,
        brains: int,
    ) -> None:
        # Recent Node releases expose fetch(), which makes this older Emscripten
        # bundle treat a local WASM path as a URL. Disable it before runMain().
        launcher = (
            "globalThis.fetch=undefined;"
            "process.argv[1]=process.argv[1];"
            "require('module').runMain()"
        )
        self.process = subprocess.Popen(
            [node, "-e", launcher, str(uci_path)],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            bufsize=1,
        )
        self.send("uci")
        uci_output = self.read_until("uciok")
        self.name = next(
            (line.removeprefix("id name ") for line in uci_output
             if line.startswith("id name ")),
            "Fairy-Stockfish",
        )
        self.send("setoption name UCI_Variant value poptactoe")
        # The published package contains no Pop Tac Toe NNUE file. Its custom
        # classical evaluator is the implementation used for this comparison.
        self.send("setoption name Use NNUE value false")
        self.send("setoption name Skill Level value 20")
        self.send(f"setoption name Threads value {brains}")
        self.send(f"setoption name Hash value {hash_megabytes}")
        self.send("isready")
        self.read_until("readyok")

    def send(self, command: str) -> None:
        if self.process.stdin is None:
            raise RuntimeError("Fairy-Stockfish stdin is closed")
        self.process.stdin.write(command + "\n")
        self.process.stdin.flush()

    def read_until(self, prefix: str) -> list[str]:
        if self.process.stdout is None:
            raise RuntimeError("Fairy-Stockfish stdout is closed")
        lines: list[str] = []
        while True:
            line = self.process.stdout.readline()
            if not line:
                raise RuntimeError("Fairy-Stockfish exited unexpectedly")
            lines.append(line.rstrip())
            if line.startswith(prefix):
                return lines

    def new_game(self) -> None:
        self.send("ucinewgame")
        self.send("isready")
        self.read_until("readyok")

    def warm_up(self, milliseconds: int) -> None:
        empty_fen = "8/8/8/8/8/8/8/8[RRRRRRRRrrrrrrrr] w - - 0 1"
        self.best_move(empty_fen, milliseconds)
        self.new_game()

    def best_move(self, fen: str, milliseconds: int) -> tuple[str, list[str]]:
        self.send("position fen " + fen)
        self.send(f"go movetime {milliseconds}")
        output = self.read_until("bestmove")
        fields = output[-1].split()
        if len(fields) < 2 or fields[1] == "(none)":
            raise RuntimeError("Fairy-Stockfish returned no move")
        return fields[1], output

    def close(self) -> None:
        if self.process.poll() is None:
            self.send("quit")
            self.process.wait(timeout=5)


def read_until_prompt_or_exit(process: subprocess.Popen[bytes]) -> tuple[str, bool]:
    if process.stdout is None:
        raise RuntimeError("challenger stdout is closed")
    chunks: list[bytes] = []
    prompt = b"you> "
    while True:
        chunk = os.read(process.stdout.fileno(), 4096)
        if not chunk:
            return b"".join(chunks).decode("utf-8", errors="replace"), True
        chunks.append(chunk)
        if prompt in b"".join(chunks[-2:]):
            return b"".join(chunks).decode("utf-8", errors="replace"), False


def stop_process(process: subprocess.Popen[bytes]) -> None:
    if process.poll() is not None:
        return
    process.terminate()
    try:
        process.wait(timeout=5)
    except subprocess.TimeoutExpired:
        process.kill()
        process.wait(timeout=5)


def latest_state(
    output: str,
) -> tuple[list[list[str]], dict[str, int], int]:
    row_pattern = re.compile(
        r"^[ \t]*([0-8]) \| ([BR.](?: [BR.]){7}) \|[ \t]*\r?$",
        re.MULTILINE,
    )
    rows = row_pattern.findall(output)
    if len(rows) < 8:
        raise RuntimeError("Could not parse the challenger board")
    latest_rows = rows[-8:]
    labels = [int(label) for label, _ in latest_rows]
    if labels == list(range(8)):
        coordinate_base = 0
    elif labels == list(range(1, 9)):
        coordinate_base = 1
    else:
        raise RuntimeError(f"Unexpected challenger row labels: {labels}")
    board = [symbols.split() for _, symbols in latest_rows]

    counts = re.findall(
        r"Blue: board=(\d+) bin=(\d+)\s+Red: board=(\d+) bin=(\d+)",
        output,
    )
    if not counts:
        raise RuntimeError("Could not parse the challenger piece counts")
    blue_board, blue_bin, red_board, red_bin = map(int, counts[-1])
    return (
        board,
        {
            "blue_board": blue_board,
            "blue_bin": blue_bin,
            "red_board": red_board,
            "red_bin": red_bin,
        },
        coordinate_base,
    )


def board_to_fen(board: list[list[str]], side: str) -> str:
    rows: list[str] = []
    for row in board:
        encoded: list[str] = []
        empty = 0
        for cell in row:
            if cell == ".":
                empty += 1
                continue
            if empty:
                encoded.append(str(empty))
                empty = 0
            encoded.append("R" if cell == "B" else "r")
        if empty:
            encoded.append(str(empty))
        rows.append("".join(encoded))

    # This mirrors the authors' published sf_agent.py adapter: the board is
    # authoritative and a full pocket is supplied for placement searches.
    return "/".join(rows) + "[RRRRRRRRrrrrrrrr] " + side + " - - 0 1"


def drop_destination(best_move: str) -> tuple[int, int]:
    match = re.search(r"@([a-h][1-8])", best_move)
    if match is None:
        raise RuntimeError(f"Expected a Fairy drop move, received {best_move!r}")
    square = match.group(1)
    return 8 - int(square[1]), ord(square[0]) - ord("a")


def play_game(
    fairy: FairyEngine,
    popplay: str,
    fairy_color: str,
    challenger_bot: str,
    fairy_ms: int,
    seed: int,
    verbose: bool,
) -> dict[str, object]:
    fairy.new_game()
    process = subprocess.Popen(
        [popplay, fairy_color, challenger_bot, "8", str(seed)],
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        bufsize=0,
    )
    transcript = ""
    moves: list[tuple[str, str]] = []
    unsupported_reason = ""
    started = time.perf_counter()
    try:
        while True:
            chunk, exited = read_until_prompt_or_exit(process)
            transcript += chunk
            for match in re.finditer(r"Computer plays ([PT][^\s]+)", chunk):
                moves.append(("challenger", match.group(1)))
            if exited:
                break

            board, counts, coordinate_base = latest_state(transcript)
            if counts["blue_bin"] == 0 or counts["red_bin"] == 0:
                unsupported_reason = (
                    "A player reached the travel phase. The published Fairy "
                    "adapter cannot encode the source checker for a King move."
                )
                break
            side = "w" if fairy_color == "blue" else "b"
            best_move, search_output = fairy.best_move(
                board_to_fen(board, side), fairy_ms
            )
            row, column = drop_destination(best_move)
            shown_row = row + coordinate_base
            shown_column = column + coordinate_base
            command = f"p {shown_row} {shown_column}"
            moves.append(("fairy", f"P({shown_row},{shown_column})"))
            if verbose:
                info = next(
                    (
                        line
                        for line in reversed(search_output)
                        if line.startswith("info depth")
                    ),
                    "",
                )
                print(
                    f"    fairy {best_move} -> "
                    f"P({shown_row},{shown_column}) {info}"
                )
            if process.stdin is None:
                raise RuntimeError("challenger stdin is closed")
            process.stdin.write((command + "\n").encode())
            process.stdin.flush()

        if not unsupported_reason:
            process.wait(timeout=5)
    finally:
        stop_process(process)

    elapsed = time.perf_counter() - started
    if unsupported_reason:
        return {
            "status": "unsupported_travel",
            "winner": "",
            "fairy_won": False,
            "draw": False,
            "plies": len(moves),
            "moves": moves,
            "seconds": elapsed,
            "message": unsupported_reason,
            "transcript": transcript,
        }

    if "Game over: Blue wins" in transcript:
        winner = "blue"
    elif "Game over: Red wins" in transcript:
        winner = "red"
    elif "Game over: draw" in transcript or "draw by" in transcript:
        winner = "draw"
    else:
        raise RuntimeError(
            "Could not identify the game result. Output tail:\n" + transcript[-2000:]
        )
    return {
        "status": "completed",
        "winner": winner,
        "fairy_won": winner == fairy_color,
        "draw": winner == "draw",
        "plies": len(moves),
        "moves": moves,
        "seconds": elapsed,
        "message": "",
        "transcript": transcript,
    }


def run_selftest() -> int:
    empty_board = [["."] * 8 for _ in range(8)]
    expected_fen = "8/8/8/8/8/8/8/8[RRRRRRRRrrrrrrrr] w - - 0 1"
    if board_to_fen(empty_board, "w") != expected_fen:
        raise RuntimeError("FEN self-test failed")
    if drop_destination("R@a8") != (0, 0):
        raise RuntimeError("a8 conversion self-test failed")
    if drop_destination("r@h1") != (7, 7):
        raise RuntimeError("h1 conversion self-test failed")

    board_cells = ". . . . . . . ."
    for coordinate_base in (0, 1):
        for newline in ("\n", "\r\n"):
            transcript = newline.join(
                f"{row + coordinate_base} | {board_cells} |"
                for row in range(8)
            )
            transcript += (
                newline
                + "Blue: board=0 bin=8   Red: board=0 bin=8"
                + newline
            )
            board, counts, parsed_base = latest_state(transcript)
            if board != empty_board or counts["blue_bin"] != 8:
                raise RuntimeError("board parser self-test failed")
            if parsed_base != coordinate_base:
                raise RuntimeError("coordinate-base self-test failed")

    print(
        "SELF_TEST_PASS fen=yes drop_coordinates=yes "
        "zero_based_ui=yes one_based_ui=yes windows_lines=yes"
    )
    return 0


def write_csv(path: Path, results: list[dict[str, object]]) -> None:
    fields = [
        "game",
        "pair",
        "seed",
        "fairy_color",
        "status",
        "winner",
        "challenger_result",
        "plies",
        "seconds",
        "moves",
        "message",
        "transcript",
    ]
    with path.open("w", newline="", encoding="utf-8") as output:
        writer = csv.DictWriter(output, fieldnames=fields)
        writer.writeheader()
        for result in results:
            writer.writerow({field: result.get(field, "") for field in fields})


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--games", type=int, default=20)
    parser.add_argument("--bot", default="ab:1000")
    parser.add_argument("--fairy-ms", type=int, default=1000)
    parser.add_argument("--popplay", default="./popplay.exe")
    parser.add_argument("--fairy-uci")
    parser.add_argument("--brains", type=int, default=1)
    parser.add_argument("--hash", type=int, default=64)
    parser.add_argument("--seed", type=int, default=123456)
    parser.add_argument("--warmup-ms", type=int, default=100)
    parser.add_argument("--csv", default="fairy_match.csv")
    parser.add_argument("--log-dir", default="fairy_match_logs")
    parser.add_argument("--no-transcripts", action="store_true")
    parser.add_argument("--node", default="node")
    parser.add_argument("--npm", default="npm")
    parser.add_argument("--verbose", action="store_true")
    parser.add_argument("--selftest", action="store_true")
    args = parser.parse_args()
    if args.games <= 0 or args.games % 2 != 0:
        parser.error("games must be a positive even number for paired colors")
    if args.fairy_ms <= 0 or args.hash <= 0 or args.warmup_ms <= 0:
        parser.error("fairy-ms, hash, and warmup-ms must be positive")
    if not 1 <= args.brains <= 512:
        parser.error("brains must be between 1 and 512")
    return args


def main() -> int:
    args = parse_args()
    if args.selftest:
        return run_selftest()

    try:
        node = executable(args.node)
        npm = executable(args.npm)
        popplay = executable(args.popplay)
        fairy_uci = resolve_fairy_uci(args.fairy_uci, npm)
        csv_path = Path(args.csv).expanduser().resolve()
        log_dir = Path(args.log_dir).expanduser().resolve()
        csv_path.parent.mkdir(parents=True, exist_ok=True)
        if not args.no_transcripts:
            log_dir.mkdir(parents=True, exist_ok=True)

        fairy = FairyEngine(node, fairy_uci, args.hash, args.brains)
        results: list[dict[str, object]] = []
        try:
            fairy.warm_up(args.warmup_ms)
            print(
                f"rules={RULES} scope=exact_until_travel games={args.games} "
                f"paired_color_seeds=yes challenger={args.bot} "
                f"fairy={fairy.name!r} fairy_ms={args.fairy_ms} "
                f"brains={args.brains} hash_mb={args.hash} "
                f"package={PACKAGE_NAME}@{PACKAGE_VERSION}",
                flush=True,
            )
            for game_index in range(args.games):
                game_number = game_index + 1
                pair = game_index // 2 + 1
                seed = args.seed + game_index // 2
                fairy_color = "blue" if game_index % 2 == 0 else "red"
                try:
                    result = play_game(
                        fairy,
                        popplay,
                        fairy_color,
                        args.bot,
                        args.fairy_ms,
                        seed,
                        args.verbose,
                    )
                except (OSError, RuntimeError, subprocess.SubprocessError) as error:
                    result = {
                        "status": "error",
                        "winner": "",
                        "fairy_won": False,
                        "draw": False,
                        "plies": 0,
                        "moves": [],
                        "seconds": 0.0,
                        "message": str(error),
                        "transcript": "",
                    }

                status = str(result["status"])
                if status == "completed":
                    label = (
                        "draw"
                        if result["draw"]
                        else "fairy_win"
                        if result["fairy_won"]
                        else "challenger_win"
                    )
                else:
                    label = status

                transcript_path = ""
                transcript = str(result.pop("transcript"))
                if not args.no_transcripts:
                    log_path = log_dir / (
                        f"game_{game_number:03d}_pair_{pair:03d}_"
                        f"fairy_{fairy_color}.txt"
                    )
                    log_path.write_text(transcript, encoding="utf-8")
                    transcript_path = str(log_path)

                result.update(
                    {
                        "game": game_number,
                        "pair": pair,
                        "seed": seed,
                        "fairy_color": fairy_color,
                        "challenger_result": label,
                        "moves": " ".join(
                            f"{owner}:{move}"
                            for owner, move in result["moves"]
                        ),
                        "transcript": transcript_path,
                    }
                )
                results.append(result)
                print(
                    f"game={game_number} pair={pair} seed={seed} "
                    f"fairy_color={fairy_color} result={label} "
                    f"winner={result['winner'] or '-'} "
                    f"plies={result['plies']} seconds={result['seconds']:.3f}",
                    flush=True,
                )
                if result["moves"]:
                    print(f"  {result['moves']}", flush=True)
                if result["message"]:
                    print(f"  note={result['message']}", flush=True)
        finally:
            fairy.close()

        write_csv(csv_path, results)
        completed = [result for result in results
                     if result["status"] == "completed"]
        fairy_wins = sum(bool(result["fairy_won"]) for result in completed)
        draws = sum(bool(result["draw"]) for result in completed)
        challenger_wins = len(completed) - fairy_wins - draws
        unsupported = sum(
            result["status"] == "unsupported_travel" for result in results
        )
        errors = sum(result["status"] == "error" for result in results)
        score = (
            (challenger_wins + 0.5 * draws) / len(completed)
            if completed
            else 0.0
        )
        print(
            f"summary requested={len(results)} completed={len(completed)} "
            f"challenger_wins={challenger_wins} fairy_wins={fairy_wins} "
            f"draws={draws} unsupported_travel={unsupported} errors={errors} "
            f"challenger_score={score:.3f} csv={csv_path}"
        )
        print(
            "result_note=unsupported_or_error_games_are_not_scored; "
            "a_match_is_strength_evidence_not_a_game_theoretic_proof"
        )
        return 0 if completed else 2
    except (OSError, RuntimeError, subprocess.SubprocessError) as error:
        print(f"MATCH_ERROR {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
