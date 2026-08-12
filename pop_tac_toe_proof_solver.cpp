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
#include <optional>
#include <stdexcept>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "pop_tac_toe_mcts.cpp"

namespace pop_tac_toe::proof {

constexpr int board_width = GameState::width;
constexpr int board_height = GameState::height;
constexpr int board_squares = static_cast<int>(GameState::board_size);
constexpr std::uint8_t no_square = 64;
constexpr std::uint16_t no_move = 0xFFFF;
constexpr int score_loss = -1;
constexpr int score_unknown = 0;
constexpr int score_win = 1;
constexpr int score_minimum = -2;
constexpr int score_maximum = 2;

struct FastMove {
    std::uint8_t from{no_square};
    std::uint8_t to{0};

    [[nodiscard]] friend constexpr bool operator==(const FastMove&,
                                                    const FastMove&) = default;
};

[[nodiscard]] constexpr std::uint16_t encode_move(FastMove move) noexcept {
    return static_cast<std::uint16_t>((static_cast<std::uint16_t>(move.from) << 6U) |
                                      move.to);
}

[[nodiscard]] constexpr FastMove decode_move(std::uint16_t encoded) noexcept {
    return {
        static_cast<std::uint8_t>((encoded >> 6U) & 0x7FU),
        static_cast<std::uint8_t>(encoded & 0x3FU),
    };
}

struct Position {
    std::uint64_t blue{0};
    std::uint64_t red{0};
    std::uint8_t blue_bin{8};
    std::uint8_t red_bin{8};
    Player side_to_move{Player::Blue};

    [[nodiscard]] friend constexpr bool operator==(const Position&,
                                                    const Position&) = default;

    [[nodiscard]] constexpr std::uint64_t occupied() const noexcept {
        return blue | red;
    }

    [[nodiscard]] constexpr std::uint64_t pieces(Player player) const noexcept {
        return player == Player::Blue ? blue : red;
    }

    [[nodiscard]] constexpr std::uint8_t bin_count(Player player) const noexcept {
        return player == Player::Blue ? blue_bin : red_bin;
    }
};

struct Geometry {
    std::array<std::array<std::uint8_t, 8>, board_squares> adjacent{};
    std::array<std::array<std::uint8_t, 8>, board_squares> destination{};
    std::array<std::array<std::uint8_t, 8>, board_squares> king_targets{};
    std::array<std::uint8_t, board_squares> king_count{};
    std::array<std::array<std::uint8_t, board_squares>, 512> maps{};
    std::array<std::array<std::uint8_t, board_squares>, 512> inverse_maps{};

    Geometry() {
        static constexpr std::array<std::array<int, 2>, 8> directions{{
            {{-1, -1}}, {{-1, 0}}, {{-1, 1}}, {{0, -1}},
            {{0, 1}}, {{1, -1}}, {{1, 0}}, {{1, 1}},
        }};

        for (int row = 0; row < board_height; ++row) {
            for (int column = 0; column < board_width; ++column) {
                const std::uint8_t center = GameState::square(row, column);
                for (std::size_t index = 0; index < directions.size(); ++index) {
                    const int delta_row = directions[index][0];
                    const int delta_column = directions[index][1];
                    adjacent[center][index] = GameState::square(
                        (row + delta_row + board_height) % board_height,
                        (column + delta_column + board_width) % board_width);
                    destination[center][index] = GameState::square(
                        (row + 2 * delta_row + 2 * board_height) % board_height,
                        (column + 2 * delta_column + 2 * board_width) % board_width);

                    const int king_row = row + delta_row;
                    const int king_column = column + delta_column;
                    if (king_row >= 0 && king_row < board_height &&
                        king_column >= 0 && king_column < board_width) {
                        king_targets[center][king_count[center]++] =
                            GameState::square(king_row, king_column);
                    }
                }
            }
        }

        for (int transform = 0; transform < 8; ++transform) {
            for (int row_shift = 0; row_shift < board_height; ++row_shift) {
                for (int column_shift = 0;
                     column_shift < board_width;
                     ++column_shift) {
                    const std::size_t map_index = static_cast<std::size_t>(
                        transform * 64 + row_shift * 8 + column_shift);
                    for (int row = 0; row < board_height; ++row) {
                        for (int column = 0; column < board_width; ++column) {
                            auto [new_row, new_column] =
                                transform_square(transform, row, column);
                            new_row = (new_row + row_shift) % board_height;
                            new_column =
                                (new_column + column_shift) % board_width;
                            const std::uint8_t source =
                                GameState::square(row, column);
                            const std::uint8_t target =
                                GameState::square(new_row, new_column);
                            maps[map_index][source] = target;
                            inverse_maps[map_index][target] = source;
                        }
                    }
                }
            }
        }
    }

    [[nodiscard]] static std::pair<int, int> transform_square(
        int transform,
        int row,
        int column) noexcept {
        constexpr int last = board_width - 1;
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

    [[nodiscard]] static const Geometry& instance() {
        static const Geometry geometry;
        return geometry;
    }
};

[[nodiscard]] std::uint64_t transform_bits(
    std::uint64_t bits,
    const std::array<std::uint8_t, board_squares>& map) noexcept {
    std::uint64_t result = 0;
    while (bits != 0) {
        const unsigned square = std::countr_zero(bits);
        result |= std::uint64_t{1} << map[square];
        bits &= bits - 1;
    }
    return result;
}

[[nodiscard]] std::uint64_t torus_shift(
    std::uint64_t bits,
    int delta_row,
    int delta_column) noexcept {
    constexpr std::uint64_t not_column_seven = 0x7F7F7F7F7F7F7F7FULL;
    constexpr std::uint64_t column_seven = 0x8080808080808080ULL;
    constexpr std::uint64_t not_column_zero = 0xFEFEFEFEFEFEFEFEULL;
    constexpr std::uint64_t column_zero = 0x0101010101010101ULL;

    while (delta_column > 0) {
        bits = ((bits & not_column_seven) << 1U) |
            ((bits & column_seven) >> 7U);
        --delta_column;
    }
    while (delta_column < 0) {
        bits = ((bits & not_column_zero) >> 1U) |
            ((bits & column_zero) << 7U);
        ++delta_column;
    }

    const int wrapped_rows = ((delta_row % board_height) + board_height) %
        board_height;
    return std::rotl(bits, wrapped_rows * board_width);
}

[[nodiscard]] bool has_torus_line(std::uint64_t pieces) noexcept {
    static constexpr std::array<std::array<int, 2>, 4> directions{{
        {{0, 1}}, {{1, 0}}, {{1, 1}}, {{1, -1}},
    }};
    for (const auto& direction : directions) {
        const std::uint64_t one =
            torus_shift(pieces, direction[0], direction[1]);
        const std::uint64_t two =
            torus_shift(one, direction[0], direction[1]);
        if ((pieces & one & two) != 0) return true;
    }
    return false;
}

struct MoveList {
    std::array<FastMove, 128> moves{};
    std::size_t size{0};

    void push(FastMove move) {
        if (size >= moves.size()) {
            throw std::overflow_error("move buffer capacity exceeded");
        }
        moves[size++] = move;
    }
};

[[nodiscard]] MoveList generate_moves(const Position& position) {
    MoveList result;
    const std::uint64_t occupied = position.occupied();
    if (position.bin_count(position.side_to_move) != 0) {
        std::uint64_t empty = ~occupied;
        while (empty != 0) {
            const unsigned target = std::countr_zero(empty);
            result.push({no_square, static_cast<std::uint8_t>(target)});
            empty &= empty - 1;
        }
        return result;
    }

    const Geometry& geometry = Geometry::instance();
    std::uint64_t movers = position.pieces(position.side_to_move);
    while (movers != 0) {
        const unsigned source = std::countr_zero(movers);
        for (std::uint8_t index = 0; index < geometry.king_count[source]; ++index) {
            const std::uint8_t target = geometry.king_targets[source][index];
            if ((occupied & (std::uint64_t{1} << target)) == 0) {
                result.push({static_cast<std::uint8_t>(source), target});
            }
        }
        movers &= movers - 1;
    }
    return result;
}

[[nodiscard]] Position apply_move(const Position& position, FastMove move) noexcept {
    Position child = position;
    const Player mover = position.side_to_move;
    std::uint64_t& mover_bits =
        mover == Player::Blue ? child.blue : child.red;

    if (move.from == no_square) {
        std::uint8_t& bin =
            mover == Player::Blue ? child.blue_bin : child.red_bin;
        --bin;
    } else {
        mover_bits &= ~(std::uint64_t{1} << move.from);
    }
    mover_bits |= std::uint64_t{1} << move.to;

    const std::uint64_t snapshot_blue = child.blue;
    const std::uint64_t snapshot_red = child.red;
    const std::uint64_t snapshot_occupied = snapshot_blue | snapshot_red;
    const Geometry& geometry = Geometry::instance();

    std::uint64_t clear = 0;
    std::uint64_t add_blue = 0;
    std::uint64_t add_red = 0;
    for (std::size_t index = 0; index < 8; ++index) {
        const std::uint8_t source = geometry.adjacent[move.to][index];
        const std::uint8_t target = geometry.destination[move.to][index];
        const std::uint64_t source_bit = std::uint64_t{1} << source;
        const std::uint64_t target_bit = std::uint64_t{1} << target;
        if ((snapshot_occupied & source_bit) == 0 ||
            (snapshot_occupied & target_bit) != 0) {
            continue;
        }
        clear |= source_bit;
        if ((snapshot_blue & source_bit) != 0) {
            add_blue |= target_bit;
        } else {
            add_red |= target_bit;
        }
    }

    child.blue = (child.blue & ~clear) | add_blue;
    child.red = (child.red & ~clear) | add_red;
    child.side_to_move = opponent(child.side_to_move);
    return child;
}

[[nodiscard]] Outcome terminal_outcome(const Position& position) {
    const bool blue_line = has_torus_line(position.blue);
    const bool red_line = has_torus_line(position.red);
    if (blue_line && red_line) return Outcome::Draw;
    if (blue_line) return Outcome::BlueWin;
    if (red_line) return Outcome::RedWin;

    // With at most 32 total checkers, a nonempty bin always has a legal
    // placement on the 64-square board. Avoid constructing a full move list at
    // every search node merely to establish mobility.
    if (position.bin_count(position.side_to_move) != 0) {
        return Outcome::Ongoing;
    }

    const Geometry& geometry = Geometry::instance();
    const std::uint64_t occupied = position.occupied();
    std::uint64_t movers = position.pieces(position.side_to_move);
    while (movers != 0) {
        const unsigned source = std::countr_zero(movers);
        for (std::uint8_t index = 0; index < geometry.king_count[source]; ++index) {
            const std::uint8_t target = geometry.king_targets[source][index];
            if ((occupied & (std::uint64_t{1} << target)) == 0) {
                return Outcome::Ongoing;
            }
        }
        movers &= movers - 1;
    }
    return Outcome::Draw;
}

[[nodiscard]] std::optional<int> terminal_score(const Position& position) {
    const Outcome outcome = terminal_outcome(position);
    if (outcome == Outcome::Ongoing) return std::nullopt;
    if (outcome == Outcome::Draw) return score_unknown;
    const Player winner = outcome == Outcome::BlueWin
        ? Player::Blue
        : Player::Red;
    return winner == position.side_to_move ? score_win : score_loss;
}

[[nodiscard]] int open_two_count(std::uint64_t pieces,
                                 std::uint64_t occupied) noexcept {
    static constexpr std::array<std::array<int, 2>, 4> directions{{
        {{0, 1}}, {{1, 0}}, {{1, 1}}, {{1, -1}},
    }};
    const std::uint64_t empty = ~occupied;
    int count = 0;
    for (const auto& direction : directions) {
        const std::uint64_t one =
            torus_shift(pieces, direction[0], direction[1]);
        const std::uint64_t two =
            torus_shift(one, direction[0], direction[1]);
        const std::uint64_t empty_one =
            torus_shift(empty, direction[0], direction[1]);
        const std::uint64_t empty_two =
            torus_shift(empty_one, direction[0], direction[1]);
        count += std::popcount(pieces & one & empty_two);
        count += std::popcount(pieces & empty_one & two);
        count += std::popcount(empty & one & two);
    }
    return count;
}

struct CanonicalKey {
    std::uint64_t blue{0};
    std::uint64_t red{0};
    std::uint8_t blue_bin{0};
    std::uint8_t red_bin{0};

    [[nodiscard]] friend constexpr bool operator==(const CanonicalKey&,
                                                    const CanonicalKey&) = default;
};

struct CanonicalForm {
    CanonicalKey key;
    std::uint16_t map_index{0};
};

[[nodiscard]] bool canonical_better(const CanonicalKey& candidate,
                                    const CanonicalKey& current) noexcept {
    const std::uint64_t candidate_occupied = candidate.blue | candidate.red;
    const std::uint64_t current_occupied = current.blue | current.red;
    if (candidate_occupied != current_occupied) {
        return candidate_occupied > current_occupied;
    }
    if (candidate.blue != current.blue) return candidate.blue > current.blue;
    return candidate.red > current.red;
}

class Canonicalizer {
public:
    [[nodiscard]] CanonicalForm operator()(const Position& position) const noexcept {
        std::uint64_t blue = position.blue;
        std::uint64_t red = position.red;
        std::uint8_t blue_bin = position.blue_bin;
        std::uint8_t red_bin = position.red_bin;
        if (position.side_to_move == Player::Red) {
            std::swap(blue, red);
            std::swap(blue_bin, red_bin);
        }

        const std::uint64_t occupied = blue | red;
        if (occupied == 0) {
            return {{0, 0, blue_bin, red_bin}, 0};
        }

        const Geometry& geometry = Geometry::instance();
        CanonicalForm best{};
        bool have_best = false;

        for (int transform = 0; transform < 8; ++transform) {
            std::uint64_t anchors = occupied;
            while (anchors != 0) {
                const unsigned source = std::countr_zero(anchors);
                const int row = static_cast<int>(source) / board_width;
                const int column = static_cast<int>(source) % board_width;
                const auto [transformed_row, transformed_column] =
                    Geometry::transform_square(transform, row, column);
                const int row_shift = (7 - transformed_row + 8) % 8;
                const int column_shift = (7 - transformed_column + 8) % 8;
                const std::uint16_t map_index = static_cast<std::uint16_t>(
                    transform * 64 + row_shift * 8 + column_shift);
                CanonicalKey candidate{
                    transform_bits(blue, geometry.maps[map_index]),
                    transform_bits(red, geometry.maps[map_index]),
                    blue_bin,
                    red_bin,
                };
                if (!have_best || canonical_better(candidate, best.key)) {
                    best = {candidate, map_index};
                    have_best = true;
                }
                anchors &= anchors - 1;
            }
        }
        return best;
    }

    [[nodiscard]] CanonicalForm exhaustive(const Position& position) const noexcept {
        std::uint64_t blue = position.blue;
        std::uint64_t red = position.red;
        std::uint8_t blue_bin = position.blue_bin;
        std::uint8_t red_bin = position.red_bin;
        if (position.side_to_move == Player::Red) {
            std::swap(blue, red);
            std::swap(blue_bin, red_bin);
        }

        const Geometry& geometry = Geometry::instance();
        CanonicalForm best{};
        bool have_best = false;
        for (std::uint16_t map_index = 0; map_index < 512; ++map_index) {
            CanonicalKey candidate{
                transform_bits(blue, geometry.maps[map_index]),
                transform_bits(red, geometry.maps[map_index]),
                blue_bin,
                red_bin,
            };
            if (!have_best || canonical_better(candidate, best.key)) {
                best = {candidate, map_index};
                have_best = true;
            }
        }
        return best;
    }

    [[nodiscard]] FastMove to_canonical(FastMove move,
                                        std::uint16_t map_index) const noexcept {
        const auto& map = Geometry::instance().maps[map_index];
        return {
            move.from == no_square ? no_square : map[move.from],
            map[move.to],
        };
    }

    [[nodiscard]] FastMove from_canonical(FastMove move,
                                          std::uint16_t map_index) const noexcept {
        const auto& map = Geometry::instance().inverse_maps[map_index];
        return {
            move.from == no_square ? no_square : map[move.from],
            map[move.to],
        };
    }

    [[nodiscard]] Position spatially_transform(const Position& position,
                                                std::uint16_t map_index) const noexcept {
        const auto& map = Geometry::instance().maps[map_index];
        Position transformed = position;
        transformed.blue = transform_bits(position.blue, map);
        transformed.red = transform_bits(position.red, map);
        return transformed;
    }
};

[[nodiscard]] std::uint64_t mix64(std::uint64_t value) noexcept {
    value += 0x9E3779B97F4A7C15ULL;
    value = (value ^ (value >> 30U)) * 0xBF58476D1CE4E5B9ULL;
    value = (value ^ (value >> 27U)) * 0x94D049BB133111EBULL;
    return value ^ (value >> 31U);
}

[[nodiscard]] std::uint64_t hash_key(const CanonicalKey& key) noexcept {
    std::uint64_t hash = mix64(key.blue);
    hash ^= std::rotl(mix64(key.red), 21);
    const std::uint64_t bins = static_cast<std::uint64_t>(key.blue_bin) |
        (static_cast<std::uint64_t>(key.red_bin) << 8U);
    return hash ^ std::rotl(mix64(bins), 43);
}

enum class Bound : std::uint8_t { Empty = 0, Exact, Lower, Upper };

struct TTEntry {
    std::uint64_t blue{0};
    std::uint64_t red{0};
    std::uint16_t best_move{no_move};
    std::uint16_t generation{0};
    std::int8_t score{0};
    std::uint8_t depth{0};
    std::uint8_t blue_bin{0};
    std::uint8_t red_bin{0};
    Bound bound{Bound::Empty};
};

class TranspositionTable {
public:
    explicit TranspositionTable(std::size_t megabytes) {
        const std::size_t requested_bytes = megabytes * 1024ULL * 1024ULL;
        std::size_t count = 1;
        while (count <= requested_bytes / sizeof(TTEntry) / 2) count *= 2;
        entries_.resize(count);
        mask_ = count - 1;
    }

    void new_generation() noexcept { ++generation_; }

    [[nodiscard]] const TTEntry* find(const CanonicalKey& key) const noexcept {
        const TTEntry& entry = entries_[hash_key(key) & mask_];
        return matches(entry, key) ? &entry : nullptr;
    }

    void store(const CanonicalKey& key,
               std::uint8_t depth,
               int score,
               Bound bound,
               std::uint16_t best_move) noexcept {
        TTEntry& entry = entries_[hash_key(key) & mask_];
        const bool same = matches(entry, key);
        if (!same && entry.bound != Bound::Empty &&
            entry.generation == generation_ && entry.depth > depth) {
            return;
        }
        if (same && entry.depth > depth && entry.bound == Bound::Exact &&
            bound != Bound::Exact) {
            return;
        }
        entry.blue = key.blue;
        entry.red = key.red;
        entry.blue_bin = key.blue_bin;
        entry.red_bin = key.red_bin;
        entry.depth = depth;
        entry.score = static_cast<std::int8_t>(score);
        entry.bound = bound;
        entry.best_move = best_move;
        entry.generation = generation_;
    }

    [[nodiscard]] std::size_t entry_count() const noexcept {
        return entries_.size();
    }

    [[nodiscard]] std::size_t bytes() const noexcept {
        return entries_.size() * sizeof(TTEntry);
    }

private:
    [[nodiscard]] static bool matches(const TTEntry& entry,
                                      const CanonicalKey& key) noexcept {
        return entry.bound != Bound::Empty &&
            entry.blue == key.blue && entry.red == key.red &&
            entry.blue_bin == key.blue_bin && entry.red_bin == key.red_bin;
    }

    std::vector<TTEntry> entries_;
    std::size_t mask_{0};
    std::uint16_t generation_{1};
};

struct SearchStats {
    std::uint64_t nodes{0};
    std::uint64_t tt_hits{0};
    std::uint64_t tt_cutoffs{0};
    std::uint64_t beta_cutoffs{0};
    std::uint64_t symmetry_skips{0};
};

struct SearchValue {
    int score{score_unknown};
    bool complete{true};
};

struct Candidate {
    FastMove move;
    Position child;
    CanonicalForm canonical_child;
    int order{0};
};

struct IterationResult {
    int score{score_unknown};
    bool complete{true};
    SearchStats stats;
    double seconds{0.0};
    std::vector<FastMove> principal_variation;
};

class ProofSolver {
public:
    ProofSolver(std::uint8_t checkers,
                std::size_t table_megabytes,
                std::uint64_t node_limit)
        : checkers_(checkers), table_(table_megabytes), node_limit_(node_limit) {
        history_.fill(0);
        for (auto& pair : killers_) pair.fill(no_move);
    }

    [[nodiscard]] IterationResult search(const Position& root,
                                         std::uint8_t depth) {
        stats_ = {};
        stopped_ = false;
        table_.new_generation();
        const auto start = std::chrono::steady_clock::now();
        // Two null-window searches answer the only questions that constitute a
        // proof: can the side to move force a win, or can the opponent force a
        // win? This prunes much more aggressively than calculating the exact
        // ternary horizon value with one wide window.
        const SearchValue win_test = negamax(
            root, depth, score_unknown, score_win, 0, nullptr);
        SearchValue loss_test{score_unknown, true};
        if (win_test.complete && win_test.score < score_win) {
            loss_test = negamax(
                root, depth, score_loss, score_unknown, 0, nullptr);
        }
        const double seconds = std::chrono::duration<double>(
            std::chrono::steady_clock::now() - start).count();

        IterationResult result;
        result.complete = win_test.complete && loss_test.complete;
        if (result.complete && win_test.score >= score_win) {
            result.score = score_win;
        } else if (result.complete && loss_test.score <= score_loss) {
            result.score = score_loss;
        } else {
            result.score = score_unknown;
        }
        result.stats = stats_;
        result.seconds = seconds;
        if (result.complete) {
            result.principal_variation = extract_pv(root, depth);
        }
        return result;
    }

    [[nodiscard]] std::size_t table_bytes() const noexcept {
        return table_.bytes();
    }

    [[nodiscard]] std::size_t table_entries() const noexcept {
        return table_.entry_count();
    }

private:
    [[nodiscard]] SearchValue negamax(
        const Position& position,
        std::uint8_t depth,
        int alpha,
        int beta,
        std::uint8_t ply,
        const CanonicalForm* known_canonical) {
        if (stopped_) return {score_unknown, false};
        if (node_limit_ != 0 && stats_.nodes >= node_limit_) {
            stopped_ = true;
            return {score_unknown, false};
        }
        ++stats_.nodes;

        if (const std::optional<int> terminal = terminal_score(position)) {
            return {*terminal, true};
        }
        if (depth == 0) return {score_unknown, true};

        const CanonicalForm canonical = known_canonical != nullptr
            ? *known_canonical
            : canonicalize_(position);
        const TTEntry* entry = table_.find(canonical.key);
        FastMove tt_move{};
        bool have_tt_move = false;
        if (entry != nullptr) {
            ++stats_.tt_hits;
            if (entry->best_move != no_move) {
                tt_move = canonicalize_.from_canonical(
                    decode_move(entry->best_move), canonical.map_index);
                have_tt_move = true;
            }
            if (entry->depth >= depth) {
                if (entry->bound == Bound::Exact) {
                    ++stats_.tt_cutoffs;
                    return {entry->score, true};
                }
                if (entry->bound == Bound::Lower && entry->score >= beta) {
                    ++stats_.tt_cutoffs;
                    return {entry->score, true};
                }
                if (entry->bound == Bound::Upper && entry->score <= alpha) {
                    ++stats_.tt_cutoffs;
                    return {entry->score, true};
                }
            }
        }

        const int original_alpha = alpha;
        const MoveList legal = generate_moves(position);
        if (legal.size == 0) return {score_unknown, true};

        std::array<Candidate, 128> candidates{};
        std::array<CanonicalKey, 128> child_keys{};
        std::size_t candidate_count = 0;
        const Player mover = position.side_to_move;

        for (std::size_t index = 0; index < legal.size; ++index) {
            const FastMove move = legal.moves[index];
            const Position child = apply_move(position, move);
            const CanonicalForm child_canonical = canonicalize_(child);

            std::size_t duplicate = candidate_count;
            for (std::size_t seen = 0; seen < candidate_count; ++seen) {
                if (child_keys[seen] == child_canonical.key) {
                    duplicate = seen;
                    break;
                }
            }
            if (duplicate != candidate_count) {
                ++stats_.symmetry_skips;
                if (have_tt_move && move == tt_move &&
                    candidates[duplicate].move != tt_move) {
                    candidates[duplicate].move = move;
                    candidates[duplicate].child = child;
                    candidates[duplicate].canonical_child = child_canonical;
                }
                continue;
            }

            const std::optional<int> child_terminal = terminal_score(child);
            if (child_terminal && *child_terminal == score_loss) {
                const FastMove canonical_move =
                    canonicalize_.to_canonical(move, canonical.map_index);
                table_.store(canonical.key,
                             depth,
                             score_win,
                             Bound::Exact,
                             encode_move(canonical_move));
                return {score_win, true};
            }

            int order = history_[encode_move(move)];
            if (have_tt_move && move == tt_move) order += 1'000'000'000;
            if (ply < killers_.size()) {
                if (encode_move(move) == killers_[ply][0]) order += 100'000'000;
                if (encode_move(move) == killers_[ply][1]) order += 90'000'000;
            }
            if (child_terminal) {
                order += *child_terminal == score_unknown
                    ? 80'000'000
                    : -80'000'000;
            } else {
                const int our_threats = open_two_count(
                    child.pieces(mover), child.occupied());
                const int their_threats = open_two_count(
                    child.pieces(opponent(mover)), child.occupied());
                order += 128 * (our_threats - their_threats);
            }

            child_keys[candidate_count] = child_canonical.key;
            candidates[candidate_count++] = {
                move, child, child_canonical, order,
            };
        }

        std::sort(candidates.begin(),
                  candidates.begin() + static_cast<std::ptrdiff_t>(candidate_count),
                  [](const Candidate& left, const Candidate& right) {
                      return left.order > right.order;
                  });

        int best_score = score_minimum;
        FastMove best_move{};
        bool have_best = false;
        bool beta_cutoff = false;

        for (std::size_t index = 0; index < candidate_count; ++index) {
            const Candidate& candidate = candidates[index];
            const SearchValue child = negamax(candidate.child,
                                              depth - 1,
                                              -beta,
                                              -alpha,
                                              ply + 1,
                                              &candidate.canonical_child);
            if (!child.complete) return {score_unknown, false};
            const int score = -child.score;
            if (!have_best || score > best_score) {
                best_score = score;
                best_move = candidate.move;
                have_best = true;
            }
            alpha = std::max(alpha, score);
            if (alpha >= beta) {
                beta_cutoff = true;
                ++stats_.beta_cutoffs;
                break;
            }
            if (best_score == score_win) break;
        }

        if (!have_best) return {score_unknown, true};

        Bound bound = Bound::Exact;
        if (best_score <= original_alpha) bound = Bound::Upper;
        if (beta_cutoff || best_score >= beta) bound = Bound::Lower;
        const FastMove canonical_best =
            canonicalize_.to_canonical(best_move, canonical.map_index);
        table_.store(canonical.key,
                     depth,
                     best_score,
                     bound,
                     encode_move(canonical_best));

        if (beta_cutoff) {
            const std::uint16_t encoded = encode_move(best_move);
            const int bonus = static_cast<int>(depth) * static_cast<int>(depth);
            history_[encoded] = std::min(history_[encoded] + bonus, 10'000'000);
            if (ply < killers_.size() && killers_[ply][0] != encoded) {
                killers_[ply][1] = killers_[ply][0];
                killers_[ply][0] = encoded;
            }
        }
        return {best_score, true};
    }

    [[nodiscard]] std::vector<FastMove> extract_pv(Position position,
                                                    std::uint8_t depth) const {
        std::vector<FastMove> pv;
        pv.reserve(depth);
        for (std::uint8_t ply = 0; ply < depth; ++ply) {
            if (terminal_score(position).has_value()) break;
            const CanonicalForm canonical = canonicalize_(position);
            const TTEntry* entry = table_.find(canonical.key);
            if (entry == nullptr || entry->best_move == no_move) break;
            const FastMove move = canonicalize_.from_canonical(
                decode_move(entry->best_move), canonical.map_index);
            const MoveList legal = generate_moves(position);
            bool found = false;
            for (std::size_t index = 0; index < legal.size; ++index) {
                if (legal.moves[index] == move) {
                    found = true;
                    break;
                }
            }
            if (!found) break;
            pv.push_back(move);
            position = apply_move(position, move);
        }
        return pv;
    }

    std::uint8_t checkers_;
    Canonicalizer canonicalize_;
    TranspositionTable table_;
    std::uint64_t node_limit_{0};
    SearchStats stats_{};
    bool stopped_{false};
    std::array<int, 4160> history_{};
    std::array<std::array<std::uint16_t, 2>, 33> killers_{};
};

constexpr std::uint32_t pn_infinity =
    std::numeric_limits<std::uint32_t>::max() / 4U;

struct ProofNumbers {
    std::uint32_t proof{1};
    std::uint32_t disproof{1};
    bool expanded{false};
    std::uint16_t best_move{no_move};

    [[nodiscard]] constexpr bool solved() const noexcept {
        return proof == 0 || disproof == 0;
    }
};

[[nodiscard]] constexpr std::uint32_t pn_add(
    std::uint32_t left,
    std::uint32_t right) noexcept {
    if (left >= pn_infinity || right >= pn_infinity ||
        left > pn_infinity - right) {
        return pn_infinity;
    }
    return left + right;
}

[[nodiscard]] constexpr std::uint32_t pn_increment(
    std::uint32_t value) noexcept {
    return value >= pn_infinity - 1 ? pn_infinity : value + 1;
}

[[nodiscard]] constexpr std::uint32_t pn_subtract_others(
    std::uint32_t threshold,
    std::uint32_t other_children) noexcept {
    if (threshold >= pn_infinity) return pn_infinity;
    return threshold > other_children ? threshold - other_children : 1;
}

struct DfpnKey {
    CanonicalKey position;
    bool target_to_move{false};

    [[nodiscard]] friend constexpr bool operator==(const DfpnKey&,
                                                    const DfpnKey&) = default;
};

[[nodiscard]] std::uint64_t hash_key(const DfpnKey& key) noexcept {
    return hash_key(key.position) ^
        std::rotl(mix64(static_cast<std::uint64_t>(key.target_to_move)), 9);
}

struct DfpnEntry {
    std::uint64_t blue{0};
    std::uint64_t red{0};
    std::uint32_t proof{1};
    std::uint32_t disproof{1};
    std::uint16_t best_move{no_move};
    std::uint16_t generation{0};
    std::uint8_t blue_bin{0};
    std::uint8_t red_bin{0};
    std::uint8_t target_to_move{0};
    std::uint8_t expanded{0};
};

static_assert(sizeof(DfpnEntry) == 32);

class DfpnTable {
public:
    explicit DfpnTable(std::size_t megabytes) {
        const std::size_t requested_bytes = megabytes * 1024ULL * 1024ULL;
        std::size_t count = 1;
        while (count <= requested_bytes / sizeof(DfpnEntry) / 2) count *= 2;
        entries_.resize(count);
        mask_ = count - 1;
    }

    void new_generation() noexcept {
        ++generation_;
        if (generation_ == 0) {
            std::fill(entries_.begin(), entries_.end(), DfpnEntry{});
            generation_ = 1;
        }
    }

    [[nodiscard]] const DfpnEntry* find(const DfpnKey& key) const noexcept {
        const DfpnEntry& entry = entries_[hash_key(key) & mask_];
        return matches(entry, key) ? &entry : nullptr;
    }

    [[nodiscard]] bool store(const DfpnKey& key,
                             const ProofNumbers& numbers) noexcept {
        DfpnEntry& entry = entries_[hash_key(key) & mask_];
        const bool collision = entry.generation == generation_ &&
            !matches(entry, key);
        entry.blue = key.position.blue;
        entry.red = key.position.red;
        entry.blue_bin = key.position.blue_bin;
        entry.red_bin = key.position.red_bin;
        entry.target_to_move = static_cast<std::uint8_t>(key.target_to_move);
        entry.proof = numbers.proof;
        entry.disproof = numbers.disproof;
        entry.expanded = static_cast<std::uint8_t>(numbers.expanded);
        entry.best_move = numbers.best_move;
        entry.generation = generation_;
        return collision;
    }

    [[nodiscard]] std::size_t entry_count() const noexcept {
        return entries_.size();
    }

    [[nodiscard]] std::size_t bytes() const noexcept {
        return entries_.size() * sizeof(DfpnEntry);
    }

private:
    [[nodiscard]] bool matches(const DfpnEntry& entry,
                               const DfpnKey& key) const noexcept {
        return entry.generation == generation_ &&
            entry.blue == key.position.blue &&
            entry.red == key.position.red &&
            entry.blue_bin == key.position.blue_bin &&
            entry.red_bin == key.position.red_bin &&
            entry.target_to_move ==
                static_cast<std::uint8_t>(key.target_to_move);
    }

    std::vector<DfpnEntry> entries_;
    std::size_t mask_{0};
    std::uint16_t generation_{1};
};

struct DfpnStats {
    std::uint64_t calls{0};
    std::uint64_t expansions{0};
    std::uint64_t generated_edges{0};
    std::uint64_t tt_hits{0};
    std::uint64_t tt_collisions{0};
    std::uint64_t symmetry_skips{0};
};

struct DfpnCandidate {
    FastMove move;
    Position child;
    CanonicalForm canonical_child;
    ProofNumbers numbers;
    int order{0};
};

struct DfpnChildren {
    std::array<DfpnCandidate, 128> candidates{};
    std::size_t size{0};
};

struct DfpnResult {
    ProofNumbers root;
    DfpnStats stats;
    bool stopped{false};
    bool saturated{false};
    double seconds{0.0};
    std::vector<FastMove> principal_variation;
};

class DfpnSolver {
public:
    DfpnSolver(Player target,
               std::size_t table_megabytes,
               std::uint64_t expansion_limit,
               bool show_progress)
        : target_(target),
          table_(table_megabytes),
          expansion_limit_(expansion_limit),
          show_progress_(show_progress) {}

    [[nodiscard]] DfpnResult search(const Position& root) {
        stats_ = {};
        stopped_ = false;
        table_.new_generation();
        start_ = std::chrono::steady_clock::now();
        next_progress_check_ = 65'536;
        next_progress_time_ = start_ + std::chrono::seconds(10);

        const CanonicalForm root_canonical = canonicalize_(root);
        dfpn(root, pn_infinity, pn_infinity, &root_canonical);
        const ProofNumbers root_numbers =
            inspect(root, &root_canonical, false);

        DfpnResult result;
        result.root = root_numbers;
        result.stats = stats_;
        result.stopped = stopped_;
        result.saturated = !root_numbers.solved() &&
            (root_numbers.proof >= pn_infinity ||
             root_numbers.disproof >= pn_infinity);
        result.seconds = std::chrono::duration<double>(
            std::chrono::steady_clock::now() - start_).count();
        if (root_numbers.solved()) {
            result.principal_variation = extract_pv(root);
        }
        return result;
    }

    [[nodiscard]] std::size_t table_bytes() const noexcept {
        return table_.bytes();
    }

    [[nodiscard]] std::size_t table_entries() const noexcept {
        return table_.entry_count();
    }

private:
    [[nodiscard]] std::optional<ProofNumbers> boundary_value(
        const Position& position) const noexcept {
        const bool blue_line = has_torus_line(position.blue);
        const bool red_line = has_torus_line(position.red);
        if (blue_line || red_line) {
            if (blue_line && red_line) {
                return ProofNumbers{pn_infinity, 0, true, no_move};
            }
            const Player winner = blue_line ? Player::Blue : Player::Red;
            if (winner == target_) {
                return ProofNumbers{0, pn_infinity, true, no_move};
            }
            return ProofNumbers{pn_infinity, 0, true, no_move};
        }

        // This solver asks only whether the target can force a terminal win
        // before travel starts. An ongoing all-on-board position is therefore
        // a disproven leaf for this specific proposition, not a game result.
        if (position.blue_bin == 0 && position.red_bin == 0) {
            return ProofNumbers{pn_infinity, 0, true, no_move};
        }
        return std::nullopt;
    }

    [[nodiscard]] DfpnKey make_key(const Position& position,
                                   const CanonicalForm& canonical) const noexcept {
        return {canonical.key, position.side_to_move == target_};
    }

    [[nodiscard]] ProofNumbers inspect(
        const Position& position,
        const CanonicalForm* known_canonical,
        bool count_hit) {
        if (const std::optional<ProofNumbers> boundary =
                boundary_value(position)) {
            return *boundary;
        }
        const CanonicalForm canonical = known_canonical != nullptr
            ? *known_canonical
            : canonicalize_(position);
        if (const DfpnEntry* entry = table_.find(make_key(position, canonical))) {
            if (count_hit) ++stats_.tt_hits;
            return {entry->proof,
                    entry->disproof,
                    entry->expanded != 0,
                    entry->best_move};
        }
        return {};
    }

    void store(const Position& position,
               const CanonicalForm& canonical,
               const ProofNumbers& numbers) noexcept {
        if (table_.store(make_key(position, canonical), numbers)) {
            ++stats_.tt_collisions;
        }
    }

    [[nodiscard]] DfpnChildren build_children(
        const Position& position,
        bool count_expansion) {
        DfpnChildren result;
        std::array<CanonicalKey, 128> keys{};
        const MoveList legal = generate_moves(position);
        const Player mover = position.side_to_move;

        for (std::size_t index = 0; index < legal.size; ++index) {
            const FastMove move = legal.moves[index];
            const Position child = apply_move(position, move);
            const CanonicalForm canonical_child = canonicalize_(child);
            std::size_t duplicate = result.size;
            for (std::size_t seen = 0; seen < result.size; ++seen) {
                if (keys[seen] == canonical_child.key) {
                    duplicate = seen;
                    break;
                }
            }
            if (duplicate != result.size) {
                if (count_expansion) ++stats_.symmetry_skips;
                continue;
            }

            int order = 0;
            if (const std::optional<ProofNumbers> boundary =
                    boundary_value(child)) {
                if (position.side_to_move == target_) {
                    order += boundary->proof == 0 ? 100'000'000 : -100'000'000;
                } else {
                    order += boundary->disproof == 0 ? 100'000'000 : -100'000'000;
                }
            } else {
                const int mover_threats = open_two_count(
                    child.pieces(mover), child.occupied());
                const int opponent_threats = open_two_count(
                    child.pieces(opponent(mover)), child.occupied());
                order += 128 * (mover_threats - opponent_threats);
            }

            keys[result.size] = canonical_child.key;
            result.candidates[result.size++] = {
                move,
                child,
                canonical_child,
                inspect(child, &canonical_child, true),
                order,
            };
        }
        if (count_expansion) stats_.generated_edges += legal.size;
        return result;
    }

    void refresh(DfpnChildren& children) {
        for (std::size_t index = 0; index < children.size; ++index) {
            DfpnCandidate& candidate = children.candidates[index];
            candidate.numbers = inspect(
                candidate.child, &candidate.canonical_child, true);
        }
    }

    struct Aggregate {
        ProofNumbers numbers;
        std::size_t selected{0};
        std::uint32_t second_metric{pn_infinity};
        std::uint32_t other_sum{0};
    };

    [[nodiscard]] Aggregate aggregate(
        const Position& position,
        const CanonicalForm& canonical,
        DfpnChildren& children) {
        refresh(children);
        if (children.size == 0) {
            const ProofNumbers disproven{pn_infinity, 0, true, no_move};
            store(position, canonical, disproven);
            return {disproven, 0, pn_infinity, 0};
        }

        const bool or_node = position.side_to_move == target_;
        std::size_t selected = 0;
        std::uint32_t best_metric = pn_infinity;
        int best_order = std::numeric_limits<int>::min();
        for (std::size_t index = 0; index < children.size; ++index) {
            const DfpnCandidate& candidate = children.candidates[index];
            const std::uint32_t metric = or_node
                ? candidate.numbers.proof
                : candidate.numbers.disproof;
            if (metric < best_metric ||
                (metric == best_metric && candidate.order > best_order)) {
                selected = index;
                best_metric = metric;
                best_order = candidate.order;
            }
        }

        std::uint32_t second_metric = pn_infinity;
        std::uint32_t other_sum = 0;
        ProofNumbers combined;
        if (or_node) {
            combined.proof = best_metric;
            combined.disproof = 0;
            for (std::size_t index = 0; index < children.size; ++index) {
                const ProofNumbers child = children.candidates[index].numbers;
                combined.disproof = pn_add(combined.disproof, child.disproof);
                if (index != selected) {
                    second_metric = std::min(second_metric, child.proof);
                    other_sum = pn_add(other_sum, child.disproof);
                }
            }
        } else {
            combined.proof = 0;
            combined.disproof = best_metric;
            for (std::size_t index = 0; index < children.size; ++index) {
                const ProofNumbers child = children.candidates[index].numbers;
                combined.proof = pn_add(combined.proof, child.proof);
                if (index != selected) {
                    second_metric = std::min(second_metric, child.disproof);
                    other_sum = pn_add(other_sum, child.proof);
                }
            }
        }
        combined.expanded = true;
        const FastMove canonical_best = canonicalize_.to_canonical(
            children.candidates[selected].move, canonical.map_index);
        combined.best_move = encode_move(canonical_best);
        store(position, canonical, combined);
        return {combined, selected, second_metric, other_sum};
    }

    void maybe_report_progress() {
        if (!show_progress_ || stats_.expansions < next_progress_check_) return;
        next_progress_check_ = stats_.expansions + 65'536;
        const auto now = std::chrono::steady_clock::now();
        if (now < next_progress_time_) return;
        const double seconds =
            std::chrono::duration<double>(now - start_).count();
        std::cout << "progress expansions=" << stats_.expansions
                  << " calls=" << stats_.calls
                  << " generated_edges=" << stats_.generated_edges
                  << " seconds=" << std::fixed << std::setprecision(3)
                  << seconds << '\n' << std::flush;
        next_progress_time_ = now + std::chrono::seconds(10);
    }

    void dfpn(const Position& position,
              std::uint32_t proof_threshold,
              std::uint32_t disproof_threshold,
              const CanonicalForm* known_canonical) {
        if (stopped_) return;
        ++stats_.calls;
        if (boundary_value(position).has_value()) return;

        const CanonicalForm canonical = known_canonical != nullptr
            ? *known_canonical
            : canonicalize_(position);
        ProofNumbers current = inspect(position, &canonical, true);
        if (current.solved() || current.proof >= proof_threshold ||
            current.disproof >= disproof_threshold) {
            return;
        }

        const bool new_expansion = !current.expanded;
        if (new_expansion) {
            if (expansion_limit_ != 0 &&
                stats_.expansions >= expansion_limit_) {
                stopped_ = true;
                return;
            }
            ++stats_.expansions;
            maybe_report_progress();
        }

        DfpnChildren children = build_children(position, new_expansion);
        Aggregate state = aggregate(position, canonical, children);
        while (!stopped_ && !state.numbers.solved() &&
               state.numbers.proof < proof_threshold &&
               state.numbers.disproof < disproof_threshold) {
            DfpnCandidate& selected = children.candidates[state.selected];
            const bool or_node = position.side_to_move == target_;
            std::uint32_t child_proof_threshold = proof_threshold;
            std::uint32_t child_disproof_threshold = disproof_threshold;
            if (or_node) {
                child_proof_threshold = std::min(
                    proof_threshold, pn_increment(state.second_metric));
                child_disproof_threshold = pn_subtract_others(
                    disproof_threshold, state.other_sum);
            } else {
                child_proof_threshold = pn_subtract_others(
                    proof_threshold, state.other_sum);
                child_disproof_threshold = std::min(
                    disproof_threshold, pn_increment(state.second_metric));
            }

            dfpn(selected.child,
                 child_proof_threshold,
                 child_disproof_threshold,
                 &selected.canonical_child);
            state = aggregate(position, canonical, children);
        }
    }

    [[nodiscard]] std::vector<FastMove> extract_pv(Position position) const {
        std::vector<FastMove> pv;
        for (int ply = 0; ply < 32; ++ply) {
            if (boundary_value(position).has_value()) break;
            const CanonicalForm canonical = canonicalize_(position);
            const DfpnEntry* entry = table_.find(make_key(position, canonical));
            if (entry == nullptr || entry->best_move == no_move) break;
            const FastMove move = canonicalize_.from_canonical(
                decode_move(entry->best_move), canonical.map_index);
            const MoveList legal = generate_moves(position);
            bool found = false;
            for (std::size_t index = 0; index < legal.size; ++index) {
                if (legal.moves[index] == move) {
                    found = true;
                    break;
                }
            }
            if (!found) break;
            pv.push_back(move);
            position = apply_move(position, move);
        }
        return pv;
    }

    Player target_;
    Canonicalizer canonicalize_;
    DfpnTable table_;
    std::uint64_t expansion_limit_{0};
    bool show_progress_{false};
    DfpnStats stats_{};
    bool stopped_{false};
    std::chrono::steady_clock::time_point start_{};
    std::chrono::steady_clock::time_point next_progress_time_{};
    std::uint64_t next_progress_check_{0};
};

[[nodiscard]] Position initial_position(std::uint8_t checkers) noexcept {
    return {0, 0, checkers, checkers, Player::Blue};
}

[[nodiscard]] Position from_reference(const GameState& state) noexcept {
    Position position;
    for (std::uint8_t square = 0; square < GameState::board_size; ++square) {
        if (state.board[square] == Player::Blue) {
            position.blue |= std::uint64_t{1} << square;
        } else if (state.board[square] == Player::Red) {
            position.red |= std::uint64_t{1} << square;
        }
    }
    position.blue_bin = static_cast<std::uint8_t>(state.blue_bin.size());
    position.red_bin = static_cast<std::uint8_t>(state.red_bin.size());
    position.side_to_move = state.next_player;
    return position;
}

[[nodiscard]] FastMove from_reference(Move move) noexcept {
    return {
        move.kind == MoveKind::PlaceFromBin ? no_square : move.from,
        move.to,
    };
}

[[nodiscard]] Move to_reference(FastMove move) noexcept {
    return {
        move.from == no_square ? MoveKind::PlaceFromBin : MoveKind::MoveOnBoard,
        move.from == no_square ? Move::no_square : move.from,
        move.to,
    };
}

[[nodiscard]] std::vector<std::uint16_t> encoded_moves(const MoveList& moves) {
    std::vector<std::uint16_t> encoded;
    encoded.reserve(moves.size);
    for (std::size_t index = 0; index < moves.size; ++index) {
        encoded.push_back(encode_move(moves.moves[index]));
    }
    std::sort(encoded.begin(), encoded.end());
    return encoded;
}

[[nodiscard]] std::vector<std::uint16_t> encoded_moves(
    const std::vector<Move>& moves) {
    std::vector<std::uint16_t> encoded;
    encoded.reserve(moves.size());
    for (const Move move : moves) encoded.push_back(encode_move(from_reference(move)));
    std::sort(encoded.begin(), encoded.end());
    return encoded;
}

class TestRng {
public:
    [[nodiscard]] std::uint64_t next() noexcept {
        state_ ^= state_ >> 12U;
        state_ ^= state_ << 25U;
        state_ ^= state_ >> 27U;
        return state_ * 0x2545F4914F6CDD1DULL;
    }

    [[nodiscard]] std::size_t index(std::size_t size) noexcept {
        return static_cast<std::size_t>(next() % size);
    }

private:
    std::uint64_t state_{0xD1FF3E3A71A1ULL};
};

void test_require(bool condition, std::string_view message) {
    if (!condition) throw std::runtime_error(std::string(message));
}

[[nodiscard]] int naive_minimax(const Position& position, std::uint8_t depth) {
    if (const std::optional<int> terminal = terminal_score(position)) {
        return *terminal;
    }
    if (depth == 0) return score_unknown;

    const MoveList legal = generate_moves(position);
    int best = score_minimum;
    for (std::size_t index = 0; index < legal.size; ++index) {
        best = std::max(
            best,
            -naive_minimax(apply_move(position, legal.moves[index]), depth - 1));
        if (best == score_win) break;
    }
    return best == score_minimum ? score_unknown : best;
}

[[nodiscard]] bool naive_forced_win_before_travel(
    const Position& position,
    Player target) {
    const bool blue_line = has_torus_line(position.blue);
    const bool red_line = has_torus_line(position.red);
    if (blue_line || red_line) {
        if (blue_line && red_line) return false;
        return (blue_line ? Player::Blue : Player::Red) == target;
    }
    if (position.blue_bin == 0 && position.red_bin == 0) return false;

    const MoveList legal = generate_moves(position);
    if (position.side_to_move == target) {
        for (std::size_t index = 0; index < legal.size; ++index) {
            if (naive_forced_win_before_travel(
                    apply_move(position, legal.moves[index]), target)) {
                return true;
            }
        }
        return false;
    }

    for (std::size_t index = 0; index < legal.size; ++index) {
        if (!naive_forced_win_before_travel(
                apply_move(position, legal.moves[index]), target)) {
            return false;
        }
    }
    return true;
}

void run_self_test(std::uint32_t games) {
    TestRng rng;
    Canonicalizer canonicalize;
    std::uint64_t compared_positions = 0;
    std::uint64_t compared_moves = 0;

    for (const std::uint8_t checkers : {std::uint8_t{3}, std::uint8_t{8}}) {
        for (std::uint32_t game = 0; game < games; ++game) {
            RuleConfig rules = RuleConfig::computer_torus();
            rules.blue_checkers = checkers;
            rules.red_checkers = checkers;
            GameState reference(rules);
            Position fast = initial_position(checkers);

            const std::uint32_t plies = 2U * checkers + 40U;
            for (std::uint32_t ply = 0; ply < plies; ++ply) {
                test_require(fast == from_reference(reference),
                             "bitboard position differs from reference state");
                test_require(terminal_outcome(fast) == reference.terminal_outcome(),
                             "terminal outcome differs from reference engine");

                const MoveList fast_moves = generate_moves(fast);
                const std::vector<Move> reference_moves = reference.get_legal_moves();
                test_require(encoded_moves(fast_moves) == encoded_moves(reference_moves),
                             "legal move set differs from reference engine");
                compared_positions += 1;
                compared_moves += fast_moves.size;
                if (fast_moves.size == 0) break;

                const CanonicalForm optimized = canonicalize(fast);
                const CanonicalForm exhaustive = canonicalize.exhaustive(fast);
                test_require(optimized.key == exhaustive.key,
                             "optimized canonicalization differs from exhaustive search");
                const std::uint16_t random_map =
                    static_cast<std::uint16_t>(rng.next() % 512);
                const Position transformed =
                    canonicalize.spatially_transform(fast, random_map);
                test_require(canonicalize(transformed).key == optimized.key,
                             "canonical key is not invariant under torus symmetry");

                const std::size_t selected = rng.index(fast_moves.size);
                const FastMove move = fast_moves.moves[selected];
                fast = apply_move(fast, move);
                reference.apply_move(to_reference(move));
            }
        }
    }

    Position tactical{
        (std::uint64_t{1} << GameState::square(3, 4)) |
            (std::uint64_t{1} << GameState::square(3, 6)) |
            (std::uint64_t{1} << GameState::square(3, 7)),
        0,
        1,
        4,
        Player::Blue,
    };
    ProofSolver tactical_solver(4, 16, 0);
    const IterationResult tactical_result = tactical_solver.search(tactical, 1);
    test_require(tactical_result.complete && tactical_result.score == score_win,
                 "one-ply forced win was not proven");
    DfpnSolver tactical_dfpn(Player::Blue, 16, 0, false);
    const DfpnResult tactical_dfpn_result = tactical_dfpn.search(tactical);
    test_require(tactical_dfpn_result.root.proof == 0,
                 "DFPN missed a one-ply forced target win");

    Position simultaneous{
        (std::uint64_t{1} << GameState::square(0, 0)) |
            (std::uint64_t{1} << GameState::square(0, 1)) |
            (std::uint64_t{1} << GameState::square(0, 2)),
        (std::uint64_t{1} << GameState::square(7, 5)) |
            (std::uint64_t{1} << GameState::square(7, 6)) |
            (std::uint64_t{1} << GameState::square(7, 7)),
        0,
        0,
        Player::Blue,
    };
    test_require(terminal_score(simultaneous) == score_unknown,
                 "simultaneous winning lines were not scored as a draw");

    ProofSolver comparison_solver(8, 16, 0);
    for (int sample = 0; sample < 16; ++sample) {
        Position position = initial_position(8);
        const int setup_plies = sample % 6;
        for (int ply = 0; ply < setup_plies; ++ply) {
            const MoveList moves = generate_moves(position);
            position = apply_move(position, moves.moves[rng.index(moves.size)]);
            if (terminal_score(position).has_value()) {
                position = initial_position(8);
                break;
            }
        }
        const int expected = naive_minimax(position, 2);
        const IterationResult actual = comparison_solver.search(position, 2);
        test_require(actual.complete && actual.score == expected,
                     "alpha-beta result differs from exhaustive minimax");
    }

    for (int sample = 0; sample < 12; ++sample) {
        Position position = initial_position(3);
        for (int ply = 0; ply < 4; ++ply) {
            const MoveList moves = generate_moves(position);
            position = apply_move(position, moves.moves[rng.index(moves.size)]);
            if (terminal_score(position).has_value()) {
                position = initial_position(3);
                ply = -1;
            }
        }
        for (const Player target : {Player::Blue, Player::Red}) {
            const bool expected =
                naive_forced_win_before_travel(position, target);
            DfpnSolver solver(target, 16, 0, false);
            const DfpnResult actual = solver.search(position);
            test_require(actual.root.solved(),
                         "DFPN did not solve a finite comparison position");
            test_require((actual.root.proof == 0) == expected,
                         "DFPN result differs from exhaustive AND/OR search");
        }
    }

    for (const Player target : {Player::Blue, Player::Red}) {
        DfpnSolver solver(target, 16, 1'000'000, false);
        const DfpnResult result = solver.search(initial_position(3));
        test_require(result.root.disproof == 0,
                     "DFPN three-checker placement result is not exact");
    }

    std::cout << "SELF_TEST_PASS games_per_checker_count=" << games
              << " compared_positions=" << compared_positions
              << " compared_legal_moves=" << compared_moves << '\n';
}

template <typename Integer>
[[nodiscard]] bool parse_integer(const char* text, Integer& value) {
    const std::string_view input(text);
    const auto result =
        std::from_chars(input.data(), input.data() + input.size(), value);
    return result.ec == std::errc{} &&
        result.ptr == input.data() + input.size();
}

[[nodiscard]] std::string move_text(FastMove move) {
    const auto square_text = [](std::uint8_t square) {
        return std::string("(") +
            std::to_string(GameState::row_of(square)) + "," +
            std::to_string(GameState::column_of(square)) + ")";
    };
    if (move.from == no_square) return "P" + square_text(move.to);
    return "T" + square_text(move.from) + "->" + square_text(move.to);
}

void print_pv(const std::vector<FastMove>& pv) {
    std::cout << " pv=";
    if (pv.empty()) {
        std::cout << "-";
        return;
    }
    for (std::size_t index = 0; index < pv.size(); ++index) {
        if (index != 0) std::cout << ' ';
        std::cout << move_text(pv[index]);
    }
}

void print_usage(const char* program) {
    std::cerr
        << "Usage:\n"
        << "  " << program
        << " [max-depth] [checkers:3-16] [tt-megabytes] [node-limit]\n"
        << "  " << program
        << " dfpn [blue|red] [checkers:3-16] [tt-megabytes]"
           " [expansion-limit]\n"
        << "  " << program << " selftest [games-per-checker-count]\n\n"
        << "The proof search is intentionally limited to the placement phase:\n"
        << "max-depth must not exceed 2 * checkers. A zero score is UNKNOWN,"
           " never a proven draw.\n"
        << "DFPN exactly asks whether its target can force a terminal win"
           " before travel.\n";
}

int run_dfpn_cli(int argc, char** argv) {
    Player target = Player::Blue;
    std::uint32_t parsed_checkers = 8;
    std::size_t table_megabytes = 512;
    std::uint64_t expansion_limit = 100'000'000;

    if (argc > 2) {
        const std::string_view target_text = argv[2];
        if (target_text == "blue") {
            target = Player::Blue;
        } else if (target_text == "red") {
            target = Player::Red;
        } else {
            print_usage(argv[0]);
            return 2;
        }
    }
    if ((argc > 3 && (!parse_integer(argv[3], parsed_checkers) ||
                      parsed_checkers < 3 || parsed_checkers > 16)) ||
        (argc > 4 && (!parse_integer(argv[4], table_megabytes) ||
                      table_megabytes == 0 || table_megabytes > 4096)) ||
        (argc > 5 && !parse_integer(argv[5], expansion_limit)) ||
        argc > 6) {
        print_usage(argv[0]);
        return 2;
    }

    const auto checkers = static_cast<std::uint8_t>(parsed_checkers);
    DfpnSolver solver(target, table_megabytes, expansion_limit, true);
    std::cout << "mode=dfpn"
              << " rules=torus+continue+move_when_all_on_board+king"
              << " target=" << (target == Player::Blue ? "blue" : "red")
              << " objective=force_terminal_win_before_travel"
              << " checkers_per_player=" << parsed_checkers
              << " tt_megabytes_requested=" << table_megabytes
              << " tt_megabytes_actual=" << std::fixed << std::setprecision(1)
              << static_cast<double>(solver.table_bytes()) / (1024.0 * 1024.0)
              << " tt_entries=" << solver.table_entries()
              << " expansion_limit=" << expansion_limit
              << " coordinates=zero_based\n" << std::flush;

    const DfpnResult result = solver.search(initial_position(checkers));
    const double expansions_per_second = result.seconds > 0.0
        ? static_cast<double>(result.stats.expansions) / result.seconds
        : 0.0;
    std::cout << "proof_number=" << result.root.proof
              << " disproof_number=" << result.root.disproof
              << " expansions=" << result.stats.expansions
              << " calls=" << result.stats.calls
              << " generated_edges=" << result.stats.generated_edges
              << " tt_hits=" << result.stats.tt_hits
              << " tt_collisions=" << result.stats.tt_collisions
              << " symmetry_skips=" << result.stats.symmetry_skips
              << " seconds=" << std::setprecision(6) << result.seconds
              << " expansions_per_second=" << std::setprecision(1)
              << expansions_per_second;
    print_pv(result.principal_variation);
    std::cout << '\n';

    if (result.root.proof == 0) {
        std::cout << "result=PROVEN_FORCED_WIN_BEFORE_TRAVEL"
                  << " target=" << (target == Player::Blue ? "blue" : "red")
                  << '\n';
        return 0;
    }
    if (result.root.disproof == 0) {
        std::cout << "result=DISPROVEN_FORCED_WIN_BEFORE_TRAVEL"
                  << " target=" << (target == Player::Blue ? "blue" : "red")
                  << " full_game_result=UNKNOWN\n";
        return 0;
    }
    std::cout << "result=UNKNOWN reason="
              << (result.stopped
                      ? "expansion_limit"
                      : result.saturated ? "proof_number_saturation"
                                         : "search_stalled")
              << " full_game_result=UNKNOWN\n";
    return 3;
}

} // namespace pop_tac_toe::proof

int main(int argc, char** argv) {
    using namespace pop_tac_toe::proof;

    if (argc > 1 && std::string_view(argv[1]) == "dfpn") {
        return run_dfpn_cli(argc, argv);
    }

    if (argc > 1 && std::string_view(argv[1]) == "selftest") {
        std::uint32_t games = 100;
        if ((argc > 2 && (!parse_integer(argv[2], games) || games == 0)) ||
            argc > 3) {
            print_usage(argv[0]);
            return 2;
        }
        try {
            run_self_test(games);
            return 0;
        } catch (const std::exception& error) {
            std::cerr << "SELF_TEST_FAIL " << error.what() << '\n';
            return 1;
        }
    }

    std::uint32_t max_depth = 8;
    std::uint32_t parsed_checkers = 8;
    std::size_t table_megabytes = 128;
    std::uint64_t node_limit = 50'000'000;
    if ((argc > 1 && (!parse_integer(argv[1], max_depth) || max_depth == 0)) ||
        (argc > 2 && (!parse_integer(argv[2], parsed_checkers) ||
                      parsed_checkers < 3 || parsed_checkers > 16)) ||
        (argc > 3 && (!parse_integer(argv[3], table_megabytes) ||
                      table_megabytes == 0 || table_megabytes > 4096)) ||
        (argc > 4 && !parse_integer(argv[4], node_limit)) ||
        argc > 5 || max_depth > 2 * parsed_checkers) {
        print_usage(argv[0]);
        return 2;
    }

    const auto checkers = static_cast<std::uint8_t>(parsed_checkers);
    ProofSolver solver(checkers, table_megabytes, node_limit);
    const Position root = initial_position(checkers);

    std::cout << "rules=torus+continue+move_when_all_on_board+king"
              << " checkers_per_player=" << parsed_checkers
              << " max_depth=" << max_depth
              << " scope=placement_phase_only"
              << " tt_megabytes_requested=" << table_megabytes
              << " tt_megabytes_actual=" << std::fixed << std::setprecision(1)
              << static_cast<double>(solver.table_bytes()) / (1024.0 * 1024.0)
              << " tt_entries=" << solver.table_entries()
              << " node_limit_per_iteration=" << node_limit << '\n';
    std::cout << "score_semantics=+1_proven_win,-1_proven_loss,0_unknown"
                 " coordinates=zero_based\n";

    int final_score = score_unknown;
    bool interrupted = false;
    std::uint32_t completed_depth = 0;
    std::vector<FastMove> final_pv;

    for (std::uint32_t depth = 1; depth <= max_depth; ++depth) {
        const IterationResult result = solver.search(root, static_cast<std::uint8_t>(depth));
        const double nps = result.seconds > 0.0
            ? static_cast<double>(result.stats.nodes) / result.seconds
            : 0.0;
        std::cout << "depth=" << depth
                  << " complete=" << (result.complete ? "yes" : "no")
                  << " score=" << result.score
                  << " nodes=" << result.stats.nodes
                  << " tt_hits=" << result.stats.tt_hits
                  << " tt_cutoffs=" << result.stats.tt_cutoffs
                  << " beta_cutoffs=" << result.stats.beta_cutoffs
                  << " symmetry_skips=" << result.stats.symmetry_skips
                  << " seconds=" << std::setprecision(6) << result.seconds
                  << " nodes_per_second=" << std::setprecision(1) << nps;
        print_pv(result.principal_variation);
        std::cout << '\n';

        if (!result.complete) {
            interrupted = true;
            break;
        }
        completed_depth = depth;
        final_score = result.score;
        final_pv = result.principal_variation;
        if (final_score != score_unknown) break;
    }

    if (interrupted) {
        std::cout << "result=UNKNOWN reason=node_limit"
                  << " last_completed_depth=" << completed_depth
                  << " travel_searched=no\n";
        return 3;
    }
    if (final_score == score_win) {
        std::cout << "result=PROVEN_WIN proof_depth=" << completed_depth
                  << " forced_terminal_before_travel=yes";
    } else if (final_score == score_loss) {
        std::cout << "result=PROVEN_LOSS proof_depth=" << completed_depth
                  << " forced_terminal_before_travel=yes";
    } else {
        std::cout << "result=UNKNOWN searched_through_depth=" << completed_depth
                  << " travel_searched=no";
    }
    if (!final_pv.empty()) {
        std::cout << " best_move=" << move_text(final_pv.front());
    }
    std::cout << '\n';
    return 0;
}
