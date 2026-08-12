#include <algorithm>
#include <bit>
#include <charconv>
#include <chrono>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <limits>
#include <optional>
#include <stdexcept>
#include <string>
#include <string_view>
#include <unordered_set>
#include <utility>
#include <vector>

#include "pop_tac_toe_mcts.cpp"
#include "pop_tac_toe_strong.cpp"

namespace pop_tac_toe::arena {

constexpr std::uint64_t default_seed = 0x504F50544143544FULL;

enum class BotKind : std::uint8_t { Random, Mcts, AlphaBeta };

struct BotSpec {
    BotKind kind{BotKind::Random};
    std::uint32_t limit{0};
    std::string text{"random"};
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
        hash ^= std::rotl(mix64(metadata), 43);
        return static_cast<std::size_t>(hash);
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

struct BotStatistics {
    std::uint64_t decisions{0};
    std::uint64_t mcts_iterations{0};
    std::uint64_t allocated_nodes{0};
    std::uint64_t alpha_beta_nodes{0};
    std::uint64_t alpha_beta_tt_hits{0};
    std::uint64_t alpha_beta_beta_cutoffs{0};
    std::uint64_t alpha_beta_completed_depth{0};
    double seconds{0.0};

    BotStatistics& operator+=(const BotStatistics& other) noexcept {
        decisions += other.decisions;
        mcts_iterations += other.mcts_iterations;
        allocated_nodes += other.allocated_nodes;
        alpha_beta_nodes += other.alpha_beta_nodes;
        alpha_beta_tt_hits += other.alpha_beta_tt_hits;
        alpha_beta_beta_cutoffs += other.alpha_beta_beta_cutoffs;
        alpha_beta_completed_depth += other.alpha_beta_completed_depth;
        seconds += other.seconds;
        return *this;
    }
};

class BotInstance {
public:
    BotInstance(BotSpec specification,
                std::uint64_t seed,
                std::uint32_t rollout_ply_limit)
        : specification_(std::move(specification)), random_(seed) {
        if (specification_.kind == BotKind::Mcts) {
            MCTSConfig config;
            config.iterations = specification_.limit;
            config.rollout_ply_limit = rollout_ply_limit;
            config.seed = seed;
            mcts_.emplace(config);
        } else if (specification_.kind == BotKind::AlphaBeta) {
            strong::AlphaBetaConfig config;
            config.time_limit_ms = specification_.limit;
            config.transposition_megabytes = 64;
            alpha_beta_.emplace(config);
        }
    }

    [[nodiscard]] Move choose(const GameState& state) {
        const auto start = std::chrono::steady_clock::now();
        Move selected;
        if (specification_.kind == BotKind::Random) {
            const std::vector<Move> legal = state.get_legal_moves();
            if (legal.empty()) {
                throw std::logic_error("random bot was asked to move in a terminal state");
            }
            selected = legal[random_.index(legal.size())];
        } else if (specification_.kind == BotKind::Mcts) {
            const std::optional<SearchResult> result = mcts_->search(state);
            if (!result.has_value()) {
                throw std::logic_error("MCTS returned no move in an ongoing state");
            }
            selected = result->move;
            statistics_.mcts_iterations += specification_.limit;
            statistics_.allocated_nodes += mcts_->nodes_allocated();
        } else {
            const std::optional<strong::AlphaBetaResult> result =
                alpha_beta_->search(state);
            if (!result.has_value()) {
                throw std::logic_error(
                    "alpha-beta returned no move in an ongoing state");
            }
            selected = result->move;
            statistics_.alpha_beta_nodes += result->stats.nodes;
            statistics_.alpha_beta_tt_hits += result->stats.tt_hits;
            statistics_.alpha_beta_beta_cutoffs +=
                result->stats.beta_cutoffs;
            statistics_.alpha_beta_completed_depth +=
                result->completed_depth;
        }
        statistics_.seconds += std::chrono::duration<double>(
            std::chrono::steady_clock::now() - start).count();
        ++statistics_.decisions;
        return selected;
    }

    [[nodiscard]] const BotStatistics& statistics() const noexcept {
        return statistics_;
    }

private:
    BotSpec specification_;
    FastRng random_;
    std::optional<MCTS> mcts_;
    std::optional<strong::AlphaBetaBot> alpha_beta_;
    BotStatistics statistics_{};
};

enum class EndReason : std::uint8_t {
    TerminalWin,
    TerminalDraw,
    Repetition,
    PlyLimit,
};

[[nodiscard]] constexpr std::string_view end_reason_text(
    EndReason reason) noexcept {
    switch (reason) {
    case EndReason::TerminalWin: return "terminal_win";
    case EndReason::TerminalDraw: return "terminal_draw";
    case EndReason::Repetition: return "repetition";
    case EndReason::PlyLimit: return "ply_limit";
    }
    return "unknown";
}

struct GameRecord {
    Outcome outcome{Outcome::Draw};
    EndReason reason{EndReason::TerminalDraw};
    std::uint32_t plies{0};
    std::uint32_t opening_plies{0};
    std::vector<Move> opening_moves;
    std::vector<Move> moves;
    BotStatistics blue_statistics;
    BotStatistics red_statistics;
};

[[nodiscard]] bool is_legal_move(const GameState& state, Move move) {
    const std::vector<Move> legal = state.get_legal_moves();
    return std::find(legal.begin(), legal.end(), move) != legal.end();
}

[[nodiscard]] std::vector<Move> make_test_opening(
    const RuleConfig& rules,
    std::uint32_t opening_plies,
    std::uint64_t seed) {
    if (opening_plies == 0) return {};

    // Restart when a random prefix reaches a position where every move ends
    // the game. This keeps every benchmark position nonterminal while still
    // making the prefix a completely legal history from the empty board.
    constexpr std::uint32_t max_attempts = 10'000;
    for (std::uint32_t attempt = 0; attempt < max_attempts; ++attempt) {
        GameState state(rules);
        FastRng random(mix64(seed + attempt));
        std::vector<Move> opening;
        opening.reserve(opening_plies);

        while (opening.size() < opening_plies) {
            const std::vector<Move> legal = state.get_legal_moves();
            std::vector<Move> nonterminal;
            nonterminal.reserve(legal.size());
            for (const Move move : legal) {
                GameState child = state;
                child.apply_move(move);
                if (child.terminal_outcome() == Outcome::Ongoing) {
                    nonterminal.push_back(move);
                }
            }
            if (nonterminal.empty()) break;
            const Move selected = nonterminal[random.index(nonterminal.size())];
            opening.push_back(selected);
            state.apply_move(selected);
        }
        if (opening.size() == opening_plies) return opening;
    }
    throw std::runtime_error("could not generate a nonterminal test opening");
}

[[nodiscard]] GameRecord play_game(const RuleConfig& rules,
                                   const BotSpec& blue_specification,
                                   const BotSpec& red_specification,
                                   std::uint64_t blue_seed,
                                   std::uint64_t red_seed,
                                   std::uint32_t max_plies,
                                   const std::vector<Move>& opening_moves = {}) {
    GameState state(rules);
    BotInstance blue(blue_specification, blue_seed, max_plies);
    BotInstance red(red_specification, red_seed, max_plies);
    std::unordered_set<ExactPositionKey, ExactPositionHash> visited;
    visited.reserve(max_plies);
    std::vector<Move> moves;
    moves.reserve(max_plies);

    for (const Move move : opening_moves) {
        if (state.terminal_outcome() != Outcome::Ongoing ||
            !visited.insert(exact_key(state)).second ||
            !is_legal_move(state, move)) {
            throw std::logic_error("test opening is not a legal nonterminal history");
        }
        moves.push_back(move);
        state.apply_move(move);
    }
    if (state.terminal_outcome() != Outcome::Ongoing) {
        throw std::logic_error("test opening ended the game");
    }

    Outcome final_outcome = Outcome::Draw;
    EndReason reason = EndReason::TerminalDraw;
    while (true) {
        const Outcome outcome = state.terminal_outcome();
        if (outcome != Outcome::Ongoing) {
            final_outcome = outcome;
            reason = outcome == Outcome::Draw
                ? EndReason::TerminalDraw
                : EndReason::TerminalWin;
            break;
        }
        if (!visited.insert(exact_key(state)).second) {
            final_outcome = Outcome::Draw;
            reason = EndReason::Repetition;
            break;
        }
        if (state.ply >= max_plies) {
            final_outcome = Outcome::Draw;
            reason = EndReason::PlyLimit;
            break;
        }

        BotInstance& bot = state.next_player == Player::Blue ? blue : red;
        const Move move = bot.choose(state);
        if (!is_legal_move(state, move)) {
            throw std::logic_error("bot returned an illegal move");
        }
        moves.push_back(move);
        state.apply_move(move);
    }

    return {
        final_outcome,
        reason,
        state.ply,
        static_cast<std::uint32_t>(opening_moves.size()),
        opening_moves,
        std::move(moves),
        blue.statistics(),
        red.statistics(),
    };
}

[[nodiscard]] std::string move_text(Move move) {
    const auto square_text = [](std::uint8_t square) {
        return std::string("(") +
            std::to_string(GameState::row_of(square) + 1) + "," +
            std::to_string(GameState::column_of(square) + 1) + ")";
    };
    if (move.kind == MoveKind::PlaceFromBin) {
        return "P" + square_text(move.to);
    }
    return "T" + square_text(move.from) + ">" + square_text(move.to);
}

[[nodiscard]] std::string move_sequence(const std::vector<Move>& moves) {
    std::string result;
    for (std::size_t index = 0; index < moves.size(); ++index) {
        if (index != 0) result.push_back(';');
        result += move_text(moves[index]);
    }
    return result;
}

[[nodiscard]] constexpr std::string_view color_text(Player player) noexcept {
    return player == Player::Blue ? "blue" : "red";
}

[[nodiscard]] constexpr std::string_view outcome_text(Outcome outcome) noexcept {
    switch (outcome) {
    case Outcome::BlueWin: return "blue_win";
    case Outcome::RedWin: return "red_win";
    case Outcome::Draw: return "draw";
    case Outcome::Ongoing: return "ongoing";
    }
    return "unknown";
}

enum class IdentityResult : std::uint8_t { AWin, BWin, Draw };

[[nodiscard]] constexpr std::string_view identity_result_text(
    IdentityResult result) noexcept {
    switch (result) {
    case IdentityResult::AWin: return "a_win";
    case IdentityResult::BWin: return "b_win";
    case IdentityResult::Draw: return "draw";
    }
    return "unknown";
}

[[nodiscard]] IdentityResult result_for_identity(Outcome outcome,
                                                 bool a_is_blue) noexcept {
    if (outcome == Outcome::Draw) return IdentityResult::Draw;
    const bool blue_won = outcome == Outcome::BlueWin;
    return blue_won == a_is_blue ? IdentityResult::AWin
                                 : IdentityResult::BWin;
}

struct ScoreBreakdown {
    std::uint64_t wins{0};
    std::uint64_t losses{0};
    std::uint64_t draws{0};

    void add(IdentityResult result) noexcept {
        if (result == IdentityResult::AWin) {
            ++wins;
        } else if (result == IdentityResult::BWin) {
            ++losses;
        } else {
            ++draws;
        }
    }

    [[nodiscard]] std::uint64_t games() const noexcept {
        return wins + losses + draws;
    }

    [[nodiscard]] double points() const noexcept {
        return static_cast<double>(wins) + 0.5 * static_cast<double>(draws);
    }

    [[nodiscard]] double score() const noexcept {
        return games() == 0 ? 0.5 : points() / static_cast<double>(games());
    }
};

class CsvWriter {
public:
    explicit CsvWriter(const std::optional<std::string>& path) {
        if (!path.has_value()) return;
        stream_.emplace(*path, std::ios::out | std::ios::trunc);
        if (!*stream_) {
            throw std::runtime_error("could not open CSV output file: " + *path);
        }
        *stream_ << "game,pair_seed,a_color,result_for_a,outcome,plies,end_reason,"
                    "start_mode,opening_plies,checkers,max_plies,blue_bot,red_bot,"
                    "blue_seconds,red_seconds,opening_moves,moves\n";
    }

    void write(std::uint32_t game,
               std::uint64_t pair_seed,
               bool a_is_blue,
               IdentityResult identity_result,
               const GameRecord& record,
               std::uint32_t checkers,
               std::uint32_t max_plies,
               std::string_view blue_bot,
               std::string_view red_bot) {
        if (!stream_.has_value()) return;
        *stream_ << game << ','
                 << pair_seed << ','
                 << (a_is_blue ? "blue" : "red") << ','
                 << identity_result_text(identity_result) << ','
                 << outcome_text(record.outcome) << ','
                 << record.plies << ','
                 << end_reason_text(record.reason) << ','
                 << (record.opening_plies == 0 ? "empty_board" : "test_opening")
                 << ','
                 << record.opening_plies << ','
                 << checkers << ','
                 << max_plies << ','
                 << blue_bot << ','
                 << red_bot << ','
                 << std::setprecision(9) << record.blue_statistics.seconds << ','
                 << std::setprecision(9) << record.red_statistics.seconds << ','
                 << '"' << move_sequence(record.opening_moves) << '"' << ','
                 << '"' << move_sequence(record.moves) << '"' << '\n';
        stream_->flush();
    }

private:
    std::optional<std::ofstream> stream_;
};

template <typename Integer>
[[nodiscard]] bool parse_integer(std::string_view text, Integer& value) {
    const auto result =
        std::from_chars(text.data(), text.data() + text.size(), value);
    return result.ec == std::errc{} && result.ptr == text.data() + text.size();
}

[[nodiscard]] std::optional<BotSpec> parse_bot(std::string_view text) {
    if (text == "random") return BotSpec{};
    if (text == "mcts") {
        return BotSpec{BotKind::Mcts, 2'000, "mcts:2000"};
    }
    constexpr std::string_view mcts_prefix = "mcts:";
    if (text.starts_with(mcts_prefix)) {
        std::uint32_t iterations = 0;
        if (!parse_integer(text.substr(mcts_prefix.size()), iterations) ||
            iterations == 0 || iterations > 100'000'000) {
            return std::nullopt;
        }
        return BotSpec{BotKind::Mcts, iterations, std::string(text)};
    }
    if (text == "ab" || text == "strong") {
        return BotSpec{BotKind::AlphaBeta, 1'000, "ab:1000"};
    }
    constexpr std::string_view alpha_beta_prefix = "ab:";
    if (!text.starts_with(alpha_beta_prefix)) return std::nullopt;
    std::uint32_t milliseconds = 0;
    if (!parse_integer(text.substr(alpha_beta_prefix.size()), milliseconds) ||
        milliseconds == 0 || milliseconds > 3'600'000) {
        return std::nullopt;
    }
    return BotSpec{BotKind::AlphaBeta, milliseconds, std::string(text)};
}

[[nodiscard]] double smoothed_elo_difference(const ScoreBreakdown& score) {
    const double probability =
        (score.points() + 0.5) / (static_cast<double>(score.games()) + 1.0);
    return 400.0 * std::log10(probability / (1.0 - probability));
}

void print_bot_statistics(std::string_view name,
                          const BotStatistics& statistics) {
    std::cout << name
              << "_decisions=" << statistics.decisions
              << ' ' << name << "_seconds=" << std::fixed
              << std::setprecision(6) << statistics.seconds;
    if (statistics.mcts_iterations != 0) {
        const double iterations_per_second = statistics.seconds > 0.0
            ? static_cast<double>(statistics.mcts_iterations) /
                  statistics.seconds
            : 0.0;
        std::cout << ' ' << name << "_mcts_iterations="
                  << statistics.mcts_iterations
                  << ' ' << name << "_iterations_per_second="
                  << std::setprecision(1) << iterations_per_second
                  << ' ' << name << "_allocated_nodes="
                  << statistics.allocated_nodes;
    }
    if (statistics.alpha_beta_nodes != 0) {
        const double nodes_per_second = statistics.seconds > 0.0
            ? static_cast<double>(statistics.alpha_beta_nodes) /
                  statistics.seconds
            : 0.0;
        const double average_depth = statistics.decisions != 0
            ? static_cast<double>(statistics.alpha_beta_completed_depth) /
                  static_cast<double>(statistics.decisions)
            : 0.0;
        std::cout << ' ' << name << "_alpha_beta_nodes="
                  << statistics.alpha_beta_nodes
                  << ' ' << name << "_nodes_per_second="
                  << std::setprecision(1) << nodes_per_second
                  << ' ' << name << "_average_completed_depth="
                  << std::setprecision(2) << average_depth
                  << ' ' << name << "_tt_hits="
                  << statistics.alpha_beta_tt_hits
                  << ' ' << name << "_beta_cutoffs="
                  << statistics.alpha_beta_beta_cutoffs;
    }
    std::cout << '\n';
}

void test_require(bool condition, std::string_view message) {
    if (!condition) throw std::runtime_error(std::string(message));
}

void run_self_test() {
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
    cycle.ply = 0;
    test_require(cycle.terminal_outcome() == Outcome::Ongoing,
                 "cycle fixture is terminal");
    const ExactPositionKey initial = exact_key(cycle);

    const std::array<Move, 4> cycle_moves{{
        {MoveKind::MoveOnBoard, GameState::square(1, 1), GameState::square(1, 2)},
        {MoveKind::MoveOnBoard, GameState::square(6, 6), GameState::square(6, 5)},
        {MoveKind::MoveOnBoard, GameState::square(1, 2), GameState::square(1, 1)},
        {MoveKind::MoveOnBoard, GameState::square(6, 5), GameState::square(6, 6)},
    }};
    for (const Move move : cycle_moves) {
        test_require(is_legal_move(cycle, move), "cycle fixture move is illegal");
        cycle.apply_move(move);
        test_require(cycle.terminal_outcome() == Outcome::Ongoing,
                     "cycle fixture became terminal");
    }
    test_require(exact_key(cycle) == initial,
                 "exact position identity failed to detect a travel cycle");

    const BotSpec random = *parse_bot("random");
    const BotSpec mcts = *parse_bot("mcts:32");
    const BotSpec alpha_beta = *parse_bot("ab:5");
    const GameRecord first = play_game(
        rules, random, random, 1234, 5678, 64);
    const GameRecord second = play_game(
        rules, random, random, 1234, 5678, 64);
    test_require(first.outcome == second.outcome &&
                     first.reason == second.reason &&
                     first.moves == second.moves,
                 "fixed seeds did not reproduce a random-vs-random game");

    const std::vector<Move> opening_a = make_test_opening(rules, 4, 4242);
    const std::vector<Move> opening_b = make_test_opening(rules, 4, 4242);
    test_require(opening_a == opening_b && opening_a.size() == 4,
                 "fixed seed did not reproduce the test opening");
    GameState opening_state(rules);
    for (const Move move : opening_a) {
        test_require(is_legal_move(opening_state, move),
                     "generated test opening contains an illegal move");
        opening_state.apply_move(move);
        test_require(opening_state.terminal_outcome() == Outcome::Ongoing,
                     "generated test opening became terminal");
    }

    GameState opening(rules);
    BotInstance search(mcts, 9999, 64);
    const Move selected = search.choose(opening);
    test_require(is_legal_move(opening, selected),
                 "MCTS self-test returned an illegal move");
    BotInstance tactical(alpha_beta, 7777, 64);
    const Move tactical_move = tactical.choose(opening);
    test_require(is_legal_move(opening, tactical_move),
                 "alpha-beta self-test returned an illegal move");
    std::cout << "SELF_TEST_PASS repetition_cycle_plies=4"
              << " deterministic_game_plies=" << first.plies
              << " deterministic_test_opening_plies=4"
              << " coordinates=1-8 mcts_iterations=32 alpha_beta_ms=5\n";
}

void print_usage(const char* program) {
    std::cerr
        << "Usage:\n"
        << "  " << program << " selftest\n"
        << "  " << program
        << " [games] [bot-a] [bot-b] [checkers:3-16] [max-plies]"
           " [seed] [csv-file] [test-opening-plies]\n\n"
        << "Bots: random, mcts, mcts:ITERATIONS, ab, or ab:MILLISECONDS.\n"
        << "Test openings default to 0, so ordinary games still start empty.\n"
        << "Example: " << program
        << " 200 ab:1000 ab:500 8 512 123456 test.csv 6\n";
}

} // namespace pop_tac_toe::arena

int main(int argc, char** argv) {
    using namespace pop_tac_toe;
    using namespace pop_tac_toe::arena;

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

    std::uint32_t games = 10;
    BotSpec bot_a{BotKind::Mcts, 2'000, "mcts:2000"};
    BotSpec bot_b{};
    std::uint32_t parsed_checkers = 8;
    std::uint32_t max_plies = 512;
    std::uint64_t seed = default_seed;
    std::optional<std::string> csv_path;
    std::uint32_t test_opening_plies = 0;

    if (argc > 1 && (!parse_integer(std::string_view(argv[1]), games) || games == 0)) {
        print_usage(argv[0]);
        return 2;
    }
    if (argc > 2) {
        const std::optional<BotSpec> parsed = parse_bot(argv[2]);
        if (!parsed.has_value()) {
            print_usage(argv[0]);
            return 2;
        }
        bot_a = *parsed;
    }
    if (argc > 3) {
        const std::optional<BotSpec> parsed = parse_bot(argv[3]);
        if (!parsed.has_value()) {
            print_usage(argv[0]);
            return 2;
        }
        bot_b = *parsed;
    }
    if ((argc > 4 &&
         (!parse_integer(std::string_view(argv[4]), parsed_checkers) ||
          parsed_checkers < 3 || parsed_checkers > 16)) ||
        (argc > 5 &&
         (!parse_integer(std::string_view(argv[5]), max_plies) ||
          max_plies == 0 || max_plies > 1'000'000)) ||
        (argc > 6 && !parse_integer(std::string_view(argv[6]), seed)) ||
        (argc > 8 &&
         (!parse_integer(std::string_view(argv[8]), test_opening_plies) ||
          test_opening_plies >= 2U * parsed_checkers)) ||
        argc > 9) {
        print_usage(argv[0]);
        return 2;
    }
    if (argc > 7 && std::string_view(argv[7]) != "-") csv_path = argv[7];
    if (test_opening_plies >= max_plies) {
        print_usage(argv[0]);
        return 2;
    }

    RuleConfig rules = RuleConfig::computer_torus();
    rules.blue_checkers = static_cast<std::uint8_t>(parsed_checkers);
    rules.red_checkers = static_cast<std::uint8_t>(parsed_checkers);

    try {
        CsvWriter csv(csv_path);
        ScoreBreakdown overall;
        ScoreBreakdown a_as_blue;
        ScoreBreakdown a_as_red;
        BotStatistics a_statistics;
        BotStatistics b_statistics;
        std::uint64_t total_plies = 0;
        std::uint64_t repetition_draws = 0;
        std::uint64_t ply_limit_draws = 0;
        std::uint64_t terminal_draws = 0;
        std::uint64_t blue_wins = 0;
        std::uint64_t red_wins = 0;

        std::cout << "rules=torus+continue+move_when_all_on_board+king"
                  << " games=" << games
                  << " bot_a=" << bot_a.text
                  << " bot_b=" << bot_b.text
                  << " checkers_per_player=" << parsed_checkers
                  << " max_plies=" << max_plies
                  << " seed=" << seed
                  << " paired_color_seeds=yes"
                  << " start_mode="
                  << (test_opening_plies == 0
                          ? "empty_board"
                          : "paired_nonterminal_test_opening")
                  << " test_opening_plies=" << test_opening_plies
                  << " csv=" << (csv_path.has_value() ? *csv_path : "none")
                  << '\n';
        if ((games % 2U) != 0) {
            std::cout << "warning=odd_game_count_has_one_extra_game_with_a_as_blue\n";
        }

        const auto arena_start = std::chrono::steady_clock::now();
        for (std::uint32_t game = 0; game < games; ++game) {
            const std::uint32_t pair_index = game / 2U;
            const std::uint64_t pair_seed = mix64(seed + pair_index);
            const std::uint64_t a_seed = mix64(pair_seed ^ 0xA11CE5EEDULL);
            const std::uint64_t b_seed = mix64(pair_seed ^ 0xB07B07B07ULL);
            const bool a_is_blue = (game % 2U) == 0;
            const std::vector<Move> opening = make_test_opening(
                rules, test_opening_plies,
                mix64(pair_seed ^ 0x0F3A1A6ULL));

            if (test_opening_plies != 0 && !a_is_blue) {
                // The second game receives this pair's exact same legal
                // history; only the bot-color assignment changes.
                const std::vector<Move> paired_opening = make_test_opening(
                    rules, test_opening_plies,
                    mix64(pair_seed ^ 0x0F3A1A6ULL));
                if (opening != paired_opening) {
                    throw std::logic_error("paired test opening was not reproducible");
                }
            }

            const BotSpec& blue_bot = a_is_blue ? bot_a : bot_b;
            const BotSpec& red_bot = a_is_blue ? bot_b : bot_a;
            const std::uint64_t blue_seed = a_is_blue ? a_seed : b_seed;
            const std::uint64_t red_seed = a_is_blue ? b_seed : a_seed;
            const GameRecord record = play_game(
                rules, blue_bot, red_bot, blue_seed, red_seed, max_plies,
                opening);
            const IdentityResult identity_result =
                result_for_identity(record.outcome, a_is_blue);

            overall.add(identity_result);
            (a_is_blue ? a_as_blue : a_as_red).add(identity_result);
            total_plies += record.plies;
            repetition_draws += record.reason == EndReason::Repetition;
            ply_limit_draws += record.reason == EndReason::PlyLimit;
            terminal_draws += record.reason == EndReason::TerminalDraw;
            blue_wins += record.outcome == Outcome::BlueWin;
            red_wins += record.outcome == Outcome::RedWin;
            if (a_is_blue) {
                a_statistics += record.blue_statistics;
                b_statistics += record.red_statistics;
            } else {
                a_statistics += record.red_statistics;
                b_statistics += record.blue_statistics;
            }

            csv.write(game + 1U,
                      pair_seed,
                      a_is_blue,
                      identity_result,
                      record,
                      parsed_checkers,
                      max_plies,
                      blue_bot.text,
                      red_bot.text);
            std::cout << "game=" << (game + 1U)
                      << " pair=" << (pair_index + 1U)
                      << " a_color=" << (a_is_blue ? "blue" : "red")
                      << " result=" << identity_result_text(identity_result)
                      << " board_outcome=" << outcome_text(record.outcome)
                      << " plies=" << record.plies
                      << " opening_plies=" << record.opening_plies
                      << " reason=" << end_reason_text(record.reason)
                      << '\n' << std::flush;
        }

        const double arena_seconds = std::chrono::duration<double>(
            std::chrono::steady_clock::now() - arena_start).count();
        std::cout << "summary a_wins=" << overall.wins
                  << " b_wins=" << overall.losses
                  << " draws=" << overall.draws
                  << " a_score=" << std::fixed << std::setprecision(6)
                  << overall.score()
                  << " smoothed_elo_a_minus_b=" << std::setprecision(1)
                  << smoothed_elo_difference(overall)
                  << " average_plies=" << std::setprecision(2)
                  << static_cast<double>(total_plies) /
                         static_cast<double>(games)
                  << " blue_wins=" << blue_wins
                  << " red_wins=" << red_wins
                  << " repetition_draws=" << repetition_draws
                  << " terminal_draws=" << terminal_draws
                  << " ply_limit_draws=" << ply_limit_draws
                  << " arena_seconds=" << std::setprecision(3)
                  << arena_seconds << '\n';
        std::cout << "a_as_blue games=" << a_as_blue.games()
                  << " wins=" << a_as_blue.wins
                  << " losses=" << a_as_blue.losses
                  << " draws=" << a_as_blue.draws
                  << " score=" << std::setprecision(6)
                  << a_as_blue.score() << '\n';
        std::cout << "a_as_red games=" << a_as_red.games()
                  << " wins=" << a_as_red.wins
                  << " losses=" << a_as_red.losses
                  << " draws=" << a_as_red.draws
                  << " score=" << std::setprecision(6)
                  << a_as_red.score() << '\n';
        print_bot_statistics("bot_a", a_statistics);
        print_bot_statistics("bot_b", b_statistics);
        std::cout << "elo_note=smoothed_strength_estimate_not_a_game_theoretic_proof\n";
        return 0;
    } catch (const std::exception& error) {
        std::cerr << "ARENA_ERROR " << error.what() << '\n';
        return 1;
    }
}
