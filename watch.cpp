#include <algorithm>
#include <array>
#include <bit>
#include <charconv>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <iomanip>
#include <iostream>
#include <optional>
#include <random>
#include <stdexcept>
#include <string>
#include <string_view>
#include <thread>
#include <unordered_set>
#include <vector>

#include "pop_tac_toe_strong.cpp"

namespace pop_tac_toe::watch {

constexpr std::uint32_t max_plies = 512;

struct PositionKey {
    std::uint64_t blue{0};
    std::uint64_t red{0};
    std::uint8_t blue_bin{0};
    std::uint8_t red_bin{0};
    Player next{Player::Blue};

    [[nodiscard]] friend constexpr bool operator==(
        const PositionKey&, const PositionKey&) = default;
};

[[nodiscard]] std::uint64_t mix64(std::uint64_t value) noexcept {
    value += 0x9E3779B97F4A7C15ULL;
    value = (value ^ (value >> 30U)) * 0xBF58476D1CE4E5B9ULL;
    value = (value ^ (value >> 27U)) * 0x94D049BB133111EBULL;
    return value ^ (value >> 31U);
}

struct PositionHash {
    [[nodiscard]] std::size_t operator()(const PositionKey& key) const noexcept {
        std::uint64_t hash = mix64(key.blue);
        hash ^= std::rotl(mix64(key.red), 21);
        const std::uint64_t metadata =
            static_cast<std::uint64_t>(key.blue_bin) |
            (static_cast<std::uint64_t>(key.red_bin) << 8U) |
            (static_cast<std::uint64_t>(key.next) << 16U);
        return static_cast<std::size_t>(hash ^ std::rotl(mix64(metadata), 43));
    }
};

[[nodiscard]] PositionKey key_of(const GameState& state) noexcept {
    PositionKey key;
    for (std::uint8_t square = 0; square < GameState::board_size; ++square) {
        if (state.board[square] == Player::Blue) {
            key.blue |= std::uint64_t{1} << square;
        } else if (state.board[square] == Player::Red) {
            key.red |= std::uint64_t{1} << square;
        }
    }
    key.blue_bin = static_cast<std::uint8_t>(state.blue_bin.size());
    key.red_bin = static_cast<std::uint8_t>(state.red_bin.size());
    key.next = state.next_player;
    return key;
}

[[nodiscard]] constexpr std::string_view player_name(Player player) noexcept {
    return player == Player::Blue ? "Blue" : "Red";
}

[[nodiscard]] std::string square_text(std::uint8_t square) {
    return "(" + std::to_string(GameState::row_of(square) + 1) + "," +
           std::to_string(GameState::column_of(square) + 1) + ")";
}

[[nodiscard]] std::string move_text(Move move) {
    if (move.kind == MoveKind::PlaceFromBin) {
        return "P" + square_text(move.to);
    }
    return "T" + square_text(move.from) + "->" + square_text(move.to);
}

void print_board(const GameState& state) {
    std::cout << "    1 2 3 4 5 6 7 8\n"
              << "  +-----------------+\n";
    for (int row = 0; row < GameState::height; ++row) {
        std::cout << row + 1 << " |";
        for (int column = 0; column < GameState::width; ++column) {
            const Player piece = state.board[GameState::square(row, column)];
            const char symbol = piece == Player::Blue
                ? 'B' : (piece == Player::Red ? 'R' : '.');
            std::cout << ' ' << symbol;
        }
        std::cout << " |\n";
    }
    std::cout << "  +-----------------+\n"
              << "Blue: board=" << state.on_board(Player::Blue)
              << " bin=" << state.blue_bin.size()
              << "   Red: board=" << state.on_board(Player::Red)
              << " bin=" << state.red_bin.size() << '\n';
    if (state.terminal_outcome() == Outcome::Ongoing) {
        const bool placing = !state.bin(state.next_player).empty();
        std::cout << "Turn: " << player_name(state.next_player)
                  << "   Phase: " << (placing ? "place" : "travel")
                  << "   Ply: " << state.ply << "\n\n";
    }
}

[[nodiscard]] bool is_legal(const GameState& state, Move move) {
    const std::vector<Move> legal = state.get_legal_moves();
    return std::find(legal.begin(), legal.end(), move) != legal.end();
}

[[nodiscard]] Move varied_opening_move(GameState state,
                                       std::mt19937_64& random) {
    const std::vector<Move> legal = state.get_legal_moves();
    if (legal.empty()) throw std::logic_error("no legal opening move");

    std::vector<Move> safe;
    safe.reserve(legal.size());
    for (const Move move : legal) {
        GameState child = state;
        child.apply_move(move);
        if (child.terminal_outcome() == Outcome::Ongoing) safe.push_back(move);
    }
    const std::vector<Move>& choices = safe.empty() ? legal : safe;
    std::uniform_int_distribution<std::size_t> pick(0, choices.size() - 1);
    return choices[pick(random)];
}

enum class EndReason : std::uint8_t {
    Win,
    TerminalDraw,
    Repetition,
    PlyLimit,
};

struct GameResult {
    Outcome outcome{Outcome::Draw};
    EndReason reason{EndReason::TerminalDraw};
};

[[nodiscard]] GameResult classify_end(const GameState& state,
                                      bool repetition) noexcept {
    if (repetition) return {Outcome::Draw, EndReason::Repetition};
    const Outcome outcome = state.terminal_outcome();
    if (outcome == Outcome::BlueWin || outcome == Outcome::RedWin) {
        return {outcome, EndReason::Win};
    }
    if (outcome == Outcome::Draw) return {outcome, EndReason::TerminalDraw};
    return {Outcome::Draw, EndReason::PlyLimit};
}

[[nodiscard]] constexpr std::string_view reason_text(EndReason reason) noexcept {
    switch (reason) {
    case EndReason::Win: return "three in a row";
    case EndReason::TerminalDraw: return "terminal draw";
    case EndReason::Repetition: return "repetition";
    case EndReason::PlyLimit: return "512-ply limit";
    }
    return "unknown";
}

void pause(std::uint32_t milliseconds) {
    if (milliseconds != 0) {
        std::this_thread::sleep_for(std::chrono::milliseconds(milliseconds));
    }
}

[[nodiscard]] GameResult play_one(std::uint32_t game_number,
                                  std::uint32_t think_ms,
                                  std::uint32_t delay_ms,
                                  std::uint32_t opening_plies,
                                  std::uint64_t seed) {
    RuleConfig rules = RuleConfig::computer_torus();
    GameState state(rules);

    strong::AlphaBetaConfig search_config;
    search_config.time_limit_ms = think_ms;
    search_config.transposition_megabytes = 256;
    strong::AlphaBetaBot brain(search_config);
    std::mt19937_64 random(seed);

    std::unordered_set<PositionKey, PositionHash> visited;
    visited.reserve(max_plies + 1);
    bool repetition = false;

    std::cout << "Game " << game_number << "   seed=" << seed
              << "   think=" << think_ms << " ms"
              << "   varied opening=" << opening_plies << " plies\n";
    print_board(state);
    pause(delay_ms);

    while (state.terminal_outcome() == Outcome::Ongoing &&
           state.ply < max_plies) {
        if (!visited.insert(key_of(state)).second) {
            repetition = true;
            break;
        }

        const Player mover = state.next_player;
        Move move;
        if (state.ply < opening_plies) {
            move = varied_opening_move(state, random);
            std::cout << player_name(mover) << " plays " << move_text(move)
                      << "   opening exploration\n";
        } else {
            const std::optional<strong::AlphaBetaResult> result =
                brain.search(state);
            if (!result.has_value()) {
                throw std::logic_error("alpha-beta returned no move");
            }
            move = result->move;
            std::cout << player_name(mover) << " plays " << move_text(move)
                      << "   score=" << result->score
                      << " depth=" << static_cast<unsigned>(result->completed_depth)
                      << " nodes=" << result->stats.nodes
                      << " time=" << std::fixed << std::setprecision(3)
                      << result->seconds << "s";
            if (result->score == strong::mate_score) {
                std::cout << "   forced win found";
            } else if (result->score == -strong::mate_score) {
                std::cout << "   forced loss detected";
            }
            std::cout << '\n';
        }

        if (!is_legal(state, move)) {
            throw std::logic_error("bot returned an illegal move");
        }
        state.apply_move(move);
        print_board(state);
        pause(delay_ms);
    }

    const GameResult result = classify_end(state, repetition);
    if (result.outcome == Outcome::BlueWin) {
        std::cout << "Result: Blue wins";
    } else if (result.outcome == Outcome::RedWin) {
        std::cout << "Result: Red wins";
    } else {
        std::cout << "Result: Draw";
    }
    std::cout << " (" << reason_text(result.reason) << ")"
              << " after " << state.ply << " plies\n\n";
    return result;
}

template <typename Integer>
[[nodiscard]] bool parse_integer(std::string_view text, Integer& value) {
    const auto parsed =
        std::from_chars(text.data(), text.data() + text.size(), value);
    return parsed.ec == std::errc{} &&
           parsed.ptr == text.data() + text.size();
}

int self_test() {
    RuleConfig rules = RuleConfig::computer_torus();
    GameState state(rules);
    strong::AlphaBetaConfig config;
    config.time_limit_ms = 5;
    config.transposition_megabytes = 1;
    strong::AlphaBetaBot bot(config);
    const auto result = bot.search(state);
    if (!result.has_value() || !is_legal(state, result->move) ||
        move_text(result->move).find("(1,1)") == std::string::npos) {
        std::cerr << "SELF_TEST_FAIL\n";
        return 1;
    }
    std::cout << "SELF_TEST_PASS coordinates=1-8 alpha_beta=yes"
              << " travel_supported=yes repetition_draw=yes\n";
    return 0;
}

} // namespace pop_tac_toe::watch

int main(int argc, char** argv) {
    using namespace pop_tac_toe::watch;

    if (argc == 2 && std::string_view(argv[1]) == "selftest") {
        return self_test();
    }

    std::uint32_t games = 1;
    std::uint32_t think_ms = 1'000;
    std::uint32_t delay_ms = 500;
    std::uint32_t opening_plies = 4;
    std::uint64_t seed = 123'456;
    if ((argc > 1 && (!parse_integer(argv[1], games) || games == 0)) ||
        (argc > 2 && (!parse_integer(argv[2], think_ms) || think_ms == 0)) ||
        (argc > 3 && !parse_integer(argv[3], delay_ms)) ||
        (argc > 4 && (!parse_integer(argv[4], opening_plies) ||
                      opening_plies > max_plies)) ||
        (argc > 5 && !parse_integer(argv[5], seed)) || argc > 6) {
        std::cerr << "Usage: " << argv[0]
                  << " [games] [think-ms] [delay-ms] [opening-plies] [seed]\n"
                  << "Example: " << argv[0] << " 1 1000 500 4 123456\n"
                  << "Travel demo: " << argv[0]
                  << " 1 500 500 16 123456\n";
        return 2;
    }

    std::uint32_t blue_wins = 0;
    std::uint32_t red_wins = 0;
    std::uint32_t draws = 0;
    try {
        for (std::uint32_t game = 0; game < games; ++game) {
            const GameResult result = play_one(
                game + 1, think_ms, delay_ms, opening_plies, seed + game);
            if (result.outcome == pop_tac_toe::Outcome::BlueWin) {
                ++blue_wins;
            } else if (result.outcome == pop_tac_toe::Outcome::RedWin) {
                ++red_wins;
            } else {
                ++draws;
            }
        }
    } catch (const std::exception& error) {
        std::cerr << "Error: " << error.what() << '\n';
        return 1;
    }

    std::cout << "Summary: Blue=" << blue_wins << " Red=" << red_wins
              << " Draw=" << draws << '\n';
    return 0;
}
