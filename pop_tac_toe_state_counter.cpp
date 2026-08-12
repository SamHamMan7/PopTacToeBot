#include <algorithm>
#include <array>
#include <bit>
#include <charconv>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <iomanip>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string_view>
#include <unordered_set>
#include <utility>
#include <vector>

#include "pop_tac_toe_mcts.cpp"

namespace {

using namespace pop_tac_toe;

enum class SymmetryMode : std::uint8_t { None, Dihedral, Torus };

struct StateKey {
    std::uint64_t blue{0};
    std::uint64_t red{0};
    std::uint8_t blue_bin{0};
    std::uint8_t red_bin{0};

    [[nodiscard]] friend bool operator==(const StateKey&, const StateKey&) = default;
};

[[nodiscard]] std::uint64_t mix64(std::uint64_t value) noexcept {
    value += 0x9E3779B97F4A7C15ULL;
    value = (value ^ (value >> 30U)) * 0xBF58476D1CE4E5B9ULL;
    value = (value ^ (value >> 27U)) * 0x94D049BB133111EBULL;
    return value ^ (value >> 31U);
}

struct StateKeyHasher {
    [[nodiscard]] std::size_t operator()(const StateKey& key) const noexcept {
        std::uint64_t hash = mix64(key.blue);
        hash ^= std::rotl(mix64(key.red), 23);
        const std::uint64_t bins = static_cast<std::uint64_t>(key.blue_bin) |
            (static_cast<std::uint64_t>(key.red_bin) << 8U);
        hash ^= std::rotl(mix64(bins), 41);
        return static_cast<std::size_t>(hash);
    }
};

[[nodiscard]] bool key_less(const StateKey& left, const StateKey& right) noexcept {
    if (left.blue != right.blue) return left.blue < right.blue;
    if (left.red != right.red) return left.red < right.red;
    if (left.blue_bin != right.blue_bin) return left.blue_bin < right.blue_bin;
    return left.red_bin < right.red_bin;
}

class Canonicalizer {
public:
    explicit Canonicalizer(SymmetryMode mode) : mode_(mode) {
        const int dihedral_count = mode == SymmetryMode::None ? 1 : 8;
        const int translation_count = mode == SymmetryMode::Torus ? 8 : 1;
        maps_.reserve(static_cast<std::size_t>(dihedral_count) *
                      translation_count * translation_count);

        for (int transform = 0; transform < dihedral_count; ++transform) {
            for (int row_shift = 0; row_shift < translation_count; ++row_shift) {
                for (int column_shift = 0;
                     column_shift < translation_count;
                     ++column_shift) {
                    std::array<std::uint8_t, GameState::board_size> map{};
                    for (int row = 0; row < GameState::height; ++row) {
                        for (int column = 0; column < GameState::width; ++column) {
                            auto [new_row, new_column] =
                                transform_square(transform, row, column);
                            new_row = (new_row + row_shift) % GameState::height;
                            new_column =
                                (new_column + column_shift) % GameState::width;
                            map[GameState::square(row, column)] =
                                GameState::square(new_row, new_column);
                        }
                    }
                    maps_.push_back(map);
                }
            }
        }
    }

    [[nodiscard]] StateKey operator()(const GameState& state) const noexcept {
        StateKey raw;
        for (std::uint8_t square = 0;
             square < GameState::board_size;
             ++square) {
            const std::uint64_t bit = std::uint64_t{1} << square;
            if (state.board[square] == Player::Blue) raw.blue |= bit;
            if (state.board[square] == Player::Red) raw.red |= bit;
        }
        raw.blue_bin = static_cast<std::uint8_t>(state.blue_bin.size());
        raw.red_bin = static_cast<std::uint8_t>(state.red_bin.size());

        // The rules are color symmetric. Relabeling the player to move as blue
        // halves the graph while preserving every legal continuation.
        if (state.next_player == Player::Red) {
            std::swap(raw.blue, raw.red);
            std::swap(raw.blue_bin, raw.red_bin);
        }

        StateKey best{
            std::numeric_limits<std::uint64_t>::max(),
            std::numeric_limits<std::uint64_t>::max(),
            raw.blue_bin,
            raw.red_bin,
        };
        for (const auto& map : maps_) {
            StateKey candidate{
                transform_bits(raw.blue, map),
                transform_bits(raw.red, map),
                raw.blue_bin,
                raw.red_bin,
            };
            if (key_less(candidate, best)) best = candidate;
        }
        return best;
    }

    [[nodiscard]] std::size_t transform_count() const noexcept {
        return maps_.size();
    }

    [[nodiscard]] SymmetryMode mode() const noexcept { return mode_; }

private:
    [[nodiscard]] static std::pair<int, int> transform_square(
        int transform,
        int row,
        int column) noexcept {
        constexpr int last = GameState::width - 1;
        switch (transform) {
        case 0: return {row, column};
        case 1: return {column, last - row};
        case 2: return {last - row, last - column};
        case 3: return {last - column, row};
        case 4: return {row, last - column};
        case 5: return {last - column, last - row};
        case 6: return {last - row, column};
        case 7: return {column, row};
        default: return {row, column};
        }
    }

    [[nodiscard]] static std::uint64_t transform_bits(
        std::uint64_t bits,
        const std::array<std::uint8_t, GameState::board_size>& map) noexcept {
        std::uint64_t transformed = 0;
        while (bits != 0) {
            const unsigned square = std::countr_zero(bits);
            transformed |= std::uint64_t{1} << map[square];
            bits &= bits - 1;
        }
        return transformed;
    }

    SymmetryMode mode_;
    std::vector<std::array<std::uint8_t, GameState::board_size>> maps_;
};

[[nodiscard]] GameState decode_state(const StateKey& key, const RuleConfig& rules) {
    GameState state(rules);
    std::fill(state.board.begin(), state.board.end(), Player::None);

    std::uint64_t blue = key.blue;
    while (blue != 0) {
        const unsigned square = std::countr_zero(blue);
        state.board[square] = Player::Blue;
        blue &= blue - 1;
    }

    std::uint64_t red = key.red;
    while (red != 0) {
        const unsigned square = std::countr_zero(red);
        state.board[square] = Player::Red;
        red &= red - 1;
    }

    state.blue_bin.assign(key.blue_bin, 1);
    state.red_bin.assign(key.red_bin, 1);
    state.next_player = Player::Blue;
    state.ply = (key.blue == 0 && key.red == 0 &&
                 key.blue_bin == rules.blue_checkers &&
                 key.red_bin == rules.red_checkers)
        ? 0
        : 1;
    return state;
}

template <typename Integer>
[[nodiscard]] bool parse_integer(const char* text, Integer& value) {
    const std::string_view input(text);
    const auto result =
        std::from_chars(input.data(), input.data() + input.size(), value);
    return result.ec == std::errc{} &&
        result.ptr == input.data() + input.size();
}

[[nodiscard]] std::string_view symmetry_name(SymmetryMode mode) noexcept {
    switch (mode) {
    case SymmetryMode::None: return "none";
    case SymmetryMode::Dihedral: return "d4";
    case SymmetryMode::Torus: return "torus";
    }
    return "unknown";
}

struct DepthMetrics {
    std::size_t frontier{0};
    std::size_t terminal{0};
    std::size_t nonterminal{0};
    std::uint64_t legal_edges{0};
    std::uint64_t revisited_edges{0};
    std::size_t new_states{0};
    std::size_t total_states{0};
};

void print_header() {
    std::cout << std::left
              << std::setw(7) << "depth"
              << std::setw(14) << "frontier"
              << std::setw(14) << "terminal"
              << std::setw(14) << "ongoing"
              << std::setw(16) << "legal_edges"
              << std::setw(16) << "revisited"
              << std::setw(14) << "new_states"
              << "total_states\n";
}

void print_metrics(std::uint32_t depth, const DepthMetrics& metrics) {
    std::cout << std::left
              << std::setw(7) << depth
              << std::setw(14) << metrics.frontier
              << std::setw(14) << metrics.terminal
              << std::setw(14) << metrics.nonterminal
              << std::setw(16) << metrics.legal_edges
              << std::setw(16) << metrics.revisited_edges
              << std::setw(14) << metrics.new_states
              << metrics.total_states << '\n';
}

void print_usage(const char* program) {
    std::cerr
        << "Usage: " << program
        << " [max-depth:0-20] [checkers:3-16] [torus|beginner]"
           " [auto|none|d4|torus] [max-states]\n"
        << "Example: " << program << " 5 3 torus auto 1000000\n";
}

} // namespace

int main(int argc, char** argv) {
    std::uint32_t max_depth = 4;
    std::uint32_t parsed_checkers = 3;
    std::string_view preset = "torus";
    std::string_view symmetry_argument = "auto";
    std::size_t max_states = 1'000'000;

    if ((argc > 1 && (!parse_integer(argv[1], max_depth) || max_depth > 20)) ||
        (argc > 2 && (!parse_integer(argv[2], parsed_checkers) ||
                      parsed_checkers < 3 || parsed_checkers > 16)) ||
        (argc > 3 && (preset = argv[3],
                      preset != "torus" && preset != "beginner")) ||
        (argc > 4 && (symmetry_argument = argv[4],
                      symmetry_argument != "auto" &&
                      symmetry_argument != "none" &&
                      symmetry_argument != "d4" &&
                      symmetry_argument != "torus")) ||
        (argc > 5 && (!parse_integer(argv[5], max_states) || max_states == 0)) ||
        argc > 6) {
        print_usage(argv[0]);
        return 2;
    }

    SymmetryMode symmetry = SymmetryMode::None;
    if (symmetry_argument == "auto") {
        symmetry = preset == "torus"
            ? SymmetryMode::Torus
            : SymmetryMode::Dihedral;
    } else if (symmetry_argument == "d4") {
        symmetry = SymmetryMode::Dihedral;
    } else if (symmetry_argument == "torus") {
        symmetry = SymmetryMode::Torus;
    }

    if (symmetry == SymmetryMode::Torus && preset != "torus") {
        std::cerr << "Torus translations are not valid symmetries for beginner edges.\n";
        return 2;
    }

    RuleConfig rules = preset == "torus"
        ? RuleConfig::computer_torus()
        : RuleConfig::beginner();
    rules.blue_checkers = static_cast<std::uint8_t>(parsed_checkers);
    rules.red_checkers = static_cast<std::uint8_t>(parsed_checkers);

    const Canonicalizer canonicalize(symmetry);
    using StateSet = std::unordered_set<StateKey, StateKeyHasher>;
    StateSet visited;
    StateSet frontier;
    const std::size_t initial_reserve = std::min<std::size_t>(max_states, 1'000'000);
    visited.reserve(initial_reserve);
    frontier.reserve(1024);

    GameState initial(rules);
    const StateKey root = canonicalize(initial);
    visited.insert(root);
    frontier.insert(root);

    std::cout << "preset=" << preset
              << " checkers_per_player=" << parsed_checkers
              << " max_depth=" << max_depth
              << " symmetry=" << symmetry_name(symmetry)
              << " spatial_transforms=" << canonicalize.transform_count()
              << " player_to_move_normalized=yes"
              << " max_states=" << max_states << '\n';
    std::cout << "Counts use exact keys; hash collisions cannot merge positions.\n";
    print_header();

    const auto start = std::chrono::steady_clock::now();
    bool state_limit_reached = false;
    bool graph_exhausted = false;
    std::uint32_t completed_depth = 0;

    for (std::uint32_t depth = 0; depth <= max_depth; ++depth) {
        DepthMetrics metrics;
        metrics.frontier = frontier.size();
        StateSet next;
        if (depth < max_depth) {
            const std::size_t reserve_hint = std::min<std::size_t>(
                max_states > visited.size() ? max_states - visited.size() : 0,
                std::max<std::size_t>(frontier.size() * 4, 1024));
            next.reserve(reserve_hint);
        }

        std::size_t processed = 0;
        for (const StateKey& key : frontier) {
            GameState state = decode_state(key, rules);
            if (state.terminal_outcome() != Outcome::Ongoing) {
                ++metrics.terminal;
                continue;
            }
            ++metrics.nonterminal;
            if (depth == max_depth) continue;

            const std::vector<Move> moves = state.get_legal_moves();
            metrics.legal_edges += moves.size();
            for (const Move& move : moves) {
                GameState child = state;
                child.apply_move(move);
                const StateKey child_key = canonicalize(child);

                if (visited.find(child_key) != visited.end()) {
                    ++metrics.revisited_edges;
                    continue;
                }
                if (visited.size() >= max_states) {
                    state_limit_reached = true;
                    break;
                }
                visited.insert(child_key);
                next.insert(child_key);
            }
            if (state_limit_reached) break;

            ++processed;
            if (processed % 250'000 == 0) {
                std::cerr << "progress depth=" << depth
                          << " processed=" << processed
                          << " total_states=" << visited.size() << '\n';
            }
        }

        metrics.new_states = next.size();
        metrics.total_states = visited.size();
        print_metrics(depth, metrics);
        completed_depth = depth;

        if (state_limit_reached) break;
        if (depth == max_depth) break;
        if (next.empty()) {
            graph_exhausted = true;
            break;
        }
        frontier = std::move(next);
    }

    const double seconds = std::chrono::duration<double>(
        std::chrono::steady_clock::now() - start).count();
    std::cout << "seconds=" << seconds
              << " states_per_second="
              << (seconds > 0.0 ? static_cast<double>(visited.size()) / seconds : 0.0)
              << '\n';

    if (state_limit_reached) {
        std::cout << "status=state_limit_reached completed_depth="
                  << completed_depth
                  << " (increase max-states or reduce depth)\n";
        return 3;
    }
    if (graph_exhausted) {
        std::cout << "status=reachable_graph_exhausted states="
                  << visited.size() << '\n';
    } else {
        std::cout << "status=depth_limit_reached counts_exact_through_depth="
                  << completed_depth << '\n';
    }
    return 0;
}
