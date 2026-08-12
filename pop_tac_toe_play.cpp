#include <algorithm>
#include <array>
#include <bit>
#include <charconv>
#include <chrono>
#include <cctype>
#include <cstddef>
#include <cstdint>
#include <iomanip>
#include <iostream>
#include <optional>
#include <sstream>
#include <stdexcept>
#include <string>
#include <string_view>
#include <unordered_set>
#include <utility>
#include <vector>

#include "pop_tac_toe_mcts.cpp"
#include "pop_tac_toe_strong.cpp"

namespace pop_tac_toe::play {

constexpr std::uint32_t game_ply_limit = 512;
constexpr std::uint64_t default_seed = 0x504F50504C41594FULL;

enum class BotKind : std::uint8_t { Mcts, AlphaBeta };

struct BotSpec {
    BotKind kind{BotKind::AlphaBeta};
    std::uint32_t limit{1'000};
    std::string text{"ab:1000"};
};

struct ExactPositionKey {
    std::uint64_t blue{0};
    std::uint64_t red{0};
    std::uint8_t blue_bin{0};
    std::uint8_t red_bin{0};
    Player next_player{Player::Blue};

    [[nodiscard]] friend constexpr bool operator==(
        const ExactPositionKey&,
        const ExactPositionKey&) = default;
};

[[nodiscard]] std::uint64_t mix64(std::uint64_t value) noexcept {
    value += 0x9E3779B97F4A7C15ULL;
    value = (value ^ (value >> 30U)) * 0xBF58476D1CE4E5B9ULL;
    value = (value ^ (value >> 27U)) * 0x94D049BB133111EBULL;
    return value ^ (value >> 31U);
}

struct ExactPositionHash {
    [[nodiscard]] std::size_t operator()(
        const ExactPositionKey& key) const noexcept {
        std::uint64_t hash = mix64(key.blue);
        hash ^= std::rotl(mix64(key.red), 21);
        const std::uint64_t metadata =
            static_cast<std::uint64_t>(key.blue_bin) |
            (static_cast<std::uint64_t>(key.red_bin) << 8U) |
            (static_cast<std::uint64_t>(key.next_player) << 16U);
        return static_cast<std::size_t>(
            hash ^ std::rotl(mix64(metadata), 43));
    }
};

[[nodiscard]] ExactPositionKey exact_key(const GameState& state) noexcept {
    ExactPositionKey key;
    for (std::uint8_t square = 0; square < GameState::board_size; ++square) {
        if (state.board[square] == Player::Blue) {
            key.blue |= std::uint64_t{1} << square;
        } else if (state.board[square] == Player::Red) {
            key.red |= std::uint64_t{1} << square;
        }
    }
    key.blue_bin = static_cast<std::uint8_t>(state.blue_bin.size());
    key.red_bin = static_cast<std::uint8_t>(state.red_bin.size());
    key.next_player = state.next_player;
    return key;
}

[[nodiscard]] constexpr std::string_view player_name(Player player) noexcept {
    switch (player) {
    case Player::Blue: return "Blue";
    case Player::Red: return "Red";
    case Player::None: return "None";
    }
    return "Unknown";
}

[[nodiscard]] constexpr char player_symbol(Player player) noexcept {
    switch (player) {
    case Player::Blue: return 'B';
    case Player::Red: return 'R';
    case Player::None: return '.';
    }
    return '?';
}

[[nodiscard]] std::string square_text(std::uint8_t square) {
    return std::string("(") +
        std::to_string(GameState::row_of(square)) + "," +
        std::to_string(GameState::column_of(square)) + ")";
}

[[nodiscard]] std::string move_text(Move move) {
    if (move.kind == MoveKind::PlaceFromBin) {
        return "P" + square_text(move.to);
    }
    return "T" + square_text(move.from) + "->" + square_text(move.to);
}

void print_board(const GameState& state, Player human) {
    std::cout << "\n     0 1 2 3 4 5 6 7\n"
              << "   +-----------------+\n";
    for (int row = 0; row < GameState::height; ++row) {
        std::cout << ' ' << row << " | ";
        for (int column = 0; column < GameState::width; ++column) {
            std::cout << player_symbol(
                state.board[GameState::square(row, column)]);
            if (column + 1 != GameState::width) std::cout << ' ';
        }
        std::cout << " |\n";
    }
    std::cout << "   +-----------------+\n"
              << "Blue: board=" << state.on_board(Player::Blue)
              << " bin=" << state.blue_bin.size()
              << "   Red: board=" << state.on_board(Player::Red)
              << " bin=" << state.red_bin.size() << '\n'
              << "Turn: " << player_name(state.next_player)
              << (state.next_player == human ? " (you)" : " (computer)")
              << "   Ply: " << state.ply << '\n';
}

void print_help() {
    std::cout
        << "Commands:\n"
        << "  p ROW COLUMN                 place a checker from your bin\n"
        << "  t FROM_ROW FROM_COL TO_ROW TO_COL\n"
        << "                               travel with a checker\n"
        << "  moves                        list every legal move\n"
        << "  history                      show moves played so far\n"
        << "  undo                         undo your last move and bot reply\n"
        << "  board                        redraw the board\n"
        << "  help                         show these commands\n"
        << "  quit                         leave the game\n"
        << "Rows and columns are zero-based: 0 through 7.\n";
}

void print_legal_moves(const GameState& state) {
    const std::vector<Move> legal = state.get_legal_moves();
    std::cout << "Legal moves: " << legal.size() << '\n';
    constexpr std::size_t moves_per_line = 8;
    for (std::size_t index = 0; index < legal.size(); ++index) {
        std::cout << std::setw(16) << std::left << move_text(legal[index]);
        if ((index + 1) % moves_per_line == 0 || index + 1 == legal.size()) {
            std::cout << '\n';
        }
    }
    std::cout << std::right;
}

struct PlayedMove {
    Player player{Player::None};
    Move move{};
};

void print_history(const std::vector<PlayedMove>& history) {
    if (history.empty()) {
        std::cout << "No moves have been played.\n";
        return;
    }
    for (std::size_t index = 0; index < history.size(); ++index) {
        std::cout << std::setw(3) << (index + 1) << ". "
                  << player_name(history[index].player) << ' '
                  << move_text(history[index].move) << '\n';
    }
}

enum class CommandKind : std::uint8_t {
    PlayMove,
    ListMoves,
    History,
    Undo,
    Board,
    Help,
    Quit,
    Invalid,
};

struct Command {
    CommandKind kind{CommandKind::Invalid};
    Move move{};
    std::string error;
};

[[nodiscard]] bool valid_coordinate(int value) noexcept {
    return value >= 0 && value < GameState::width;
}

[[nodiscard]] bool has_extra_input(std::istringstream& stream) {
    std::string extra;
    return static_cast<bool>(stream >> extra);
}

[[nodiscard]] Command parse_command(std::string line) {
    std::istringstream stream(std::move(line));
    std::string verb;
    if (!(stream >> verb)) return {CommandKind::Invalid, {}, "Enter a command."};
    std::transform(verb.begin(), verb.end(), verb.begin(),
                   [](unsigned char character) {
                       return static_cast<char>(std::tolower(character));
                   });

    if (verb == "p" || verb == "place") {
        int row = -1;
        int column = -1;
        if (!(stream >> row >> column) || has_extra_input(stream)) {
            return {CommandKind::Invalid, {}, "Usage: p ROW COLUMN"};
        }
        if (!valid_coordinate(row) || !valid_coordinate(column)) {
            return {CommandKind::Invalid, {}, "Rows and columns must be 0 through 7."};
        }
        return {
            CommandKind::PlayMove,
            {MoveKind::PlaceFromBin, Move::no_square,
             GameState::square(row, column)},
            {},
        };
    }

    if (verb == "t" || verb == "travel") {
        int from_row = -1;
        int from_column = -1;
        int to_row = -1;
        int to_column = -1;
        if (!(stream >> from_row >> from_column >> to_row >> to_column) ||
            has_extra_input(stream)) {
            return {
                CommandKind::Invalid,
                {},
                "Usage: t FROM_ROW FROM_COL TO_ROW TO_COL",
            };
        }
        if (!valid_coordinate(from_row) || !valid_coordinate(from_column) ||
            !valid_coordinate(to_row) || !valid_coordinate(to_column)) {
            return {CommandKind::Invalid, {}, "Rows and columns must be 0 through 7."};
        }
        return {
            CommandKind::PlayMove,
            {MoveKind::MoveOnBoard,
             GameState::square(from_row, from_column),
             GameState::square(to_row, to_column)},
            {},
        };
    }

    const auto simple = [&](CommandKind kind) -> Command {
        if (has_extra_input(stream)) {
            return {CommandKind::Invalid, {}, "That command takes no arguments."};
        }
        return {kind, {}, {}};
    };
    if (verb == "moves" || verb == "legal") {
        return simple(CommandKind::ListMoves);
    }
    if (verb == "history") return simple(CommandKind::History);
    if (verb == "undo" || verb == "u") return simple(CommandKind::Undo);
    if (verb == "board") return simple(CommandKind::Board);
    if (verb == "help" || verb == "h" || verb == "?") {
        return simple(CommandKind::Help);
    }
    if (verb == "quit" || verb == "q" || verb == "exit") {
        return simple(CommandKind::Quit);
    }
    return {CommandKind::Invalid, {}, "Unknown command. Type help."};
}

[[nodiscard]] bool is_legal(const GameState& state, Move move) {
    const std::vector<Move> legal = state.get_legal_moves();
    return std::find(legal.begin(), legal.end(), move) != legal.end();
}

using VisitedSet = std::unordered_set<ExactPositionKey, ExactPositionHash>;

void rebuild_visited(const std::vector<GameState>& positions,
                     VisitedSet& visited) {
    visited.clear();
    visited.reserve(game_ply_limit + 1U);
    for (const GameState& position : positions) {
        visited.insert(exact_key(position));
    }
}

[[nodiscard]] bool undo_to_previous_human_turn(
    Player human,
    GameState& state,
    std::vector<GameState>& positions,
    std::vector<PlayedMove>& history,
    VisitedSet& visited) {
    if (positions.size() <= 1) return false;
    for (std::size_t index = positions.size() - 1; index-- > 0;) {
        if (positions[index].next_player != human ||
            positions[index].terminal_outcome() != Outcome::Ongoing) {
            continue;
        }
        positions.resize(index + 1);
        history.resize(index);
        state = positions.back();
        rebuild_visited(positions, visited);
        return true;
    }
    return false;
}

void record_move(GameState& state,
                 Move move,
                 std::vector<GameState>& positions,
                 std::vector<PlayedMove>& history) {
    const Player mover = state.next_player;
    state.apply_move(move);
    history.push_back({mover, move});
    positions.push_back(state);
}

[[nodiscard]] std::optional<Player> winner_from_outcome(Outcome outcome) {
    if (outcome == Outcome::BlueWin) return Player::Blue;
    if (outcome == Outcome::RedWin) return Player::Red;
    return std::nullopt;
}

void print_game_result(Outcome outcome, Player human) {
    if (outcome == Outcome::Draw) {
        std::cout << "Game over: draw.\n";
        return;
    }
    const Player winner = *winner_from_outcome(outcome);
    std::cout << "Game over: " << player_name(winner) << " wins"
              << (winner == human ? " — you won!\n" : " — computer won.\n");
}

template <typename Integer>
[[nodiscard]] bool parse_integer(const char* text, Integer& value) {
    const std::string_view input(text);
    const auto result =
        std::from_chars(input.data(), input.data() + input.size(), value);
    return result.ec == std::errc{} &&
        result.ptr == input.data() + input.size();
}

template <typename Integer>
[[nodiscard]] bool parse_integer(std::string_view text, Integer& value) {
    const auto result =
        std::from_chars(text.data(), text.data() + text.size(), value);
    return result.ec == std::errc{} &&
        result.ptr == text.data() + text.size();
}

[[nodiscard]] std::optional<BotSpec> parse_bot(std::string_view text) {
    std::uint32_t numeric_iterations = 0;
    if (parse_integer(text, numeric_iterations)) {
        if (numeric_iterations == 0 || numeric_iterations > 100'000'000) {
            return std::nullopt;
        }
        return BotSpec{
            BotKind::Mcts,
            numeric_iterations,
            "mcts:" + std::to_string(numeric_iterations),
        };
    }
    if (text == "mcts") return BotSpec{BotKind::Mcts, 100'000, "mcts:100000"};
    if (text == "ab" || text == "strong") {
        return BotSpec{BotKind::AlphaBeta, 1'000, "ab:1000"};
    }

    constexpr std::string_view mcts_prefix = "mcts:";
    constexpr std::string_view alpha_beta_prefix = "ab:";
    BotKind kind;
    std::string_view number;
    std::uint32_t maximum;
    if (text.starts_with(mcts_prefix)) {
        kind = BotKind::Mcts;
        number = text.substr(mcts_prefix.size());
        maximum = 100'000'000;
    } else if (text.starts_with(alpha_beta_prefix)) {
        kind = BotKind::AlphaBeta;
        number = text.substr(alpha_beta_prefix.size());
        maximum = 3'600'000;
    } else {
        return std::nullopt;
    }

    std::uint32_t limit = 0;
    if (!parse_integer(number, limit) || limit == 0 || limit > maximum) {
        return std::nullopt;
    }
    return BotSpec{kind, limit, std::string(text)};
}

void test_require(bool condition, std::string_view message) {
    if (!condition) throw std::runtime_error(std::string(message));
}

void run_self_test() {
    const Command placement = parse_command("p 3 4");
    test_require(placement.kind == CommandKind::PlayMove &&
                     placement.move.kind == MoveKind::PlaceFromBin &&
                     placement.move.to == GameState::square(3, 4),
                 "placement parser failed");
    const Command travel = parse_command("T 1 2 2 3");
    test_require(travel.kind == CommandKind::PlayMove &&
                     travel.move.kind == MoveKind::MoveOnBoard &&
                     travel.move.from == GameState::square(1, 2) &&
                     travel.move.to == GameState::square(2, 3),
                 "travel parser failed");
    test_require(parse_command("p 8 0").kind == CommandKind::Invalid,
                 "out-of-range coordinate was accepted");

    RuleConfig rules = RuleConfig::computer_torus();
    rules.blue_checkers = 3;
    rules.red_checkers = 3;
    GameState cycle(rules);
    cycle.blue_bin.clear();
    cycle.red_bin.clear();
    cycle.board.assign(GameState::board_size, Player::None);
    cycle.board[GameState::square(1, 1)] = Player::Blue;
    cycle.board[GameState::square(1, 6)] = Player::Blue;
    cycle.board[GameState::square(6, 1)] = Player::Blue;
    cycle.board[GameState::square(6, 6)] = Player::Red;
    cycle.board[GameState::square(3, 3)] = Player::Red;
    cycle.board[GameState::square(4, 5)] = Player::Red;
    cycle.next_player = Player::Blue;
    const ExactPositionKey before_cycle = exact_key(cycle);
    const std::array<Move, 4> cycle_moves{{
        {MoveKind::MoveOnBoard, GameState::square(1, 1), GameState::square(1, 2)},
        {MoveKind::MoveOnBoard, GameState::square(6, 6), GameState::square(6, 5)},
        {MoveKind::MoveOnBoard, GameState::square(1, 2), GameState::square(1, 1)},
        {MoveKind::MoveOnBoard, GameState::square(6, 5), GameState::square(6, 6)},
    }};
    for (const Move move : cycle_moves) {
        test_require(is_legal(cycle, move), "travel cycle contains an illegal move");
        cycle.apply_move(move);
    }
    test_require(exact_key(cycle) == before_cycle,
                 "exact repetition identity failed");

    RuleConfig undo_rules = RuleConfig::computer_torus();
    GameState undo_state(undo_rules);
    std::vector<GameState> positions{undo_state};
    std::vector<PlayedMove> history;
    VisitedSet visited;
    rebuild_visited(positions, visited);
    record_move(undo_state,
                {MoveKind::PlaceFromBin, Move::no_square,
                 GameState::square(0, 0)},
                positions,
                history);
    record_move(undo_state,
                {MoveKind::PlaceFromBin, Move::no_square,
                 GameState::square(4, 4)},
                positions,
                history);
    test_require(undo_to_previous_human_turn(
                     Player::Blue, undo_state, positions, history, visited),
                 "undo did not find the previous human turn");
    test_require(undo_state.ply == 0 && history.empty() && positions.size() == 1,
                 "undo did not restore the initial position");

    MCTSConfig config;
    config.iterations = 32;
    config.rollout_ply_limit = 64;
    config.seed = 12345;
    MCTS search(config);
    const std::optional<SearchResult> result = search.search(undo_state);
    test_require(result.has_value() && is_legal(undo_state, result->move),
                 "MCTS returned no legal move");

    strong::AlphaBetaConfig alpha_beta_config;
    alpha_beta_config.time_limit_ms = 5;
    alpha_beta_config.transposition_megabytes = 1;
    strong::AlphaBetaBot alpha_beta(alpha_beta_config);
    const std::optional<strong::AlphaBetaResult> alpha_beta_result =
        alpha_beta.search(undo_state);
    test_require(alpha_beta_result.has_value() &&
                     is_legal(undo_state, alpha_beta_result->move),
                 "alpha-beta returned no legal move");

    std::cout << "SELF_TEST_PASS command_parser=yes repetition_cycle_plies=4"
                 " undo=yes mcts_iterations=32 alpha_beta_ms=5\n";
}

void print_usage(const char* program) {
    std::cerr
        << "Usage:\n"
        << "  " << program << " selftest\n"
        << "  " << program
        << " [blue|red] [bot] [checkers:3-16] [seed]\n\n"
        << "Bots: ab, ab:MILLISECONDS, mcts, mcts:ITERATIONS.\n"
        << "A bare number remains shorthand for MCTS iterations.\n"
        << "Example: " << program << " blue ab:3000\n";
}

} // namespace pop_tac_toe::play

int main(int argc, char** argv) {
    using namespace pop_tac_toe;
    using namespace pop_tac_toe::play;

    if (argc > 1 && std::string_view(argv[1]) == "selftest") {
        if (argc != 2) {
            print_usage(argv[0]);
            return 2;
        }
        try {
            run_self_test();
            return 0;
        } catch (const std::exception& error) {
            std::cerr << "SELF_TEST_FAIL " << error.what() << '\n';
            return 1;
        }
    }

    Player human = Player::Blue;
    BotSpec bot;
    std::uint32_t parsed_checkers = 8;
    std::uint64_t seed = default_seed;
    if (argc > 1) {
        const std::string_view color = argv[1];
        if (color == "blue") {
            human = Player::Blue;
        } else if (color == "red") {
            human = Player::Red;
        } else {
            print_usage(argv[0]);
            return 2;
        }
    }
    if (argc > 2) {
        const std::optional<BotSpec> parsed = parse_bot(argv[2]);
        if (!parsed.has_value()) {
            print_usage(argv[0]);
            return 2;
        }
        bot = *parsed;
    }
    if ((argc > 3 && (!parse_integer(argv[3], parsed_checkers) ||
                      parsed_checkers < 3 || parsed_checkers > 16)) ||
        (argc > 4 && !parse_integer(argv[4], seed)) || argc > 5) {
        print_usage(argv[0]);
        return 2;
    }

    RuleConfig rules = RuleConfig::computer_torus();
    rules.blue_checkers = static_cast<std::uint8_t>(parsed_checkers);
    rules.red_checkers = static_cast<std::uint8_t>(parsed_checkers);
    GameState state(rules);

    std::optional<MCTS> mcts;
    std::optional<strong::AlphaBetaBot> alpha_beta;
    if (bot.kind == BotKind::Mcts) {
        MCTSConfig search_config;
        search_config.iterations = bot.limit;
        search_config.rollout_ply_limit = game_ply_limit;
        search_config.seed = seed;
        mcts.emplace(search_config);
    } else {
        strong::AlphaBetaConfig search_config;
        search_config.time_limit_ms = bot.limit;
        search_config.transposition_megabytes = 64;
        alpha_beta.emplace(search_config);
    }

    std::vector<GameState> positions{state};
    std::vector<PlayedMove> history;
    VisitedSet visited;
    rebuild_visited(positions, visited);

    std::cout << "Pop Tac Toe — terminal play\n"
              << "Rules: Torus, Continue, Move When All On Board, King\n"
              << "You are " << player_name(human) << " ("
              << player_symbol(human) << "); computer is "
              << player_name(opponent(human)) << " ("
              << player_symbol(opponent(human)) << ").\n"
              << "Checkers per player: " << parsed_checkers
              << "   Computer: " << bot.text
              << "   Seed: " << seed << '\n';
    print_help();

    while (true) {
        print_board(state, human);
        const Outcome outcome = state.terminal_outcome();
        if (outcome != Outcome::Ongoing) {
            print_game_result(outcome, human);
            break;
        }
        if (state.ply >= game_ply_limit) {
            std::cout << "Game over: draw by the " << game_ply_limit
                      << "-ply safety limit.\n";
            break;
        }

        bool position_advanced = false;
        if (state.next_player == human) {
            bool turn_completed = false;
            while (!turn_completed) {
                std::cout << "you> " << std::flush;
                std::string line;
                if (!std::getline(std::cin, line)) {
                    std::cout << "\nInput closed; leaving game.\n";
                    return 0;
                }
                const Command command = parse_command(std::move(line));
                switch (command.kind) {
                case CommandKind::PlayMove:
                    if (!is_legal(state, command.move)) {
                        std::cout << "Illegal move for this position. "
                                     "Type moves to see legal choices.\n";
                        break;
                    }
                    std::cout << "You play " << move_text(command.move) << ".\n";
                    record_move(state, command.move, positions, history);
                    position_advanced = true;
                    turn_completed = true;
                    break;
                case CommandKind::ListMoves:
                    print_legal_moves(state);
                    break;
                case CommandKind::History:
                    print_history(history);
                    break;
                case CommandKind::Undo:
                    if (undo_to_previous_human_turn(
                            human, state, positions, history, visited)) {
                        std::cout << "Undid your previous turn.\n";
                        turn_completed = true;
                    } else {
                        std::cout << "There is no previous human turn to undo.\n";
                    }
                    break;
                case CommandKind::Board:
                    print_board(state, human);
                    break;
                case CommandKind::Help:
                    print_help();
                    break;
                case CommandKind::Quit:
                    std::cout << "Game ended by user.\n";
                    return 0;
                case CommandKind::Invalid:
                    std::cout << command.error << '\n';
                    break;
                }
            }
        } else {
            std::cout << "Computer is thinking..." << std::flush;
            const auto start = std::chrono::steady_clock::now();
            std::optional<SearchResult> mcts_result;
            std::optional<strong::AlphaBetaResult> alpha_beta_result;
            Move computer_move;
            if (bot.kind == BotKind::Mcts) {
                mcts_result = mcts->search(state);
                if (mcts_result.has_value()) computer_move = mcts_result->move;
            } else {
                alpha_beta_result = alpha_beta->search(state);
                if (alpha_beta_result.has_value()) {
                    computer_move = alpha_beta_result->move;
                }
            }
            const double seconds = std::chrono::duration<double>(
                std::chrono::steady_clock::now() - start).count();
            if (!mcts_result.has_value() && !alpha_beta_result.has_value()) {
                std::cerr << "\nERROR: computer found no move in an ongoing position.\n";
                return 1;
            }
            if (!is_legal(state, computer_move)) {
                std::cerr << "\nERROR: computer returned an illegal move.\n";
                return 1;
            }
            std::cout << " done\nComputer plays " << move_text(computer_move);
            if (mcts_result.has_value()) {
                std::cout << "   visits=" << mcts_result->visits
                          << " rollout_score=" << std::fixed
                          << std::setprecision(3)
                          << mcts_result->expected_score
                          << "   nodes=" << mcts->nodes_allocated();
            } else {
                std::cout << "   score=" << alpha_beta_result->score
                          << " depth="
                          << static_cast<unsigned>(
                                 alpha_beta_result->completed_depth)
                          << " nodes=" << alpha_beta_result->stats.nodes
                          << " tt_hits=" << alpha_beta_result->stats.tt_hits;
            }
            std::cout << "   search_seconds=" << std::fixed
                      << std::setprecision(3) << seconds << '\n';
            record_move(state, computer_move, positions, history);
            position_advanced = true;
        }

        if (position_advanced &&
            state.terminal_outcome() == Outcome::Ongoing &&
            !visited.insert(exact_key(state)).second) {
            print_board(state, human);
            std::cout << "Game over: draw by repeated position.\n";
            break;
        }
    }
    std::cout << "Moves played: " << history.size() << '\n';
    return 0;
}
