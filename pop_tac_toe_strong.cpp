#include <algorithm>
#include <array>
#include <bit>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <limits>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

#include "pop_tac_toe_mcts.cpp"

namespace pop_tac_toe::strong {

constexpr std::uint8_t no_square = 64;
constexpr std::uint16_t no_move = 0xFFFF;
constexpr int mate_score = 1'000'000;
constexpr int infinity = 2'000'000;

struct FastMove {
    std::uint8_t from{no_square};
    std::uint8_t to{0};

    [[nodiscard]] friend constexpr bool operator==(
        const FastMove&, const FastMove&) = default;
};

[[nodiscard]] constexpr std::uint16_t encode_move(FastMove move) noexcept {
    return static_cast<std::uint16_t>(
        (static_cast<std::uint16_t>(move.from) << 6U) | move.to);
}

[[nodiscard]] constexpr FastMove decode_move(std::uint16_t encoded) noexcept {
    return {
        static_cast<std::uint8_t>((encoded >> 6U) & 0x7FU),
        static_cast<std::uint8_t>(encoded & 0x3FU),
    };
}

[[nodiscard]] constexpr Move to_game_move(FastMove move) noexcept {
    return move.from == no_square
        ? Move{MoveKind::PlaceFromBin, Move::no_square, move.to}
        : Move{MoveKind::MoveOnBoard, move.from, move.to};
}

struct Position {
    std::uint64_t blue{0};
    std::uint64_t red{0};
    std::uint8_t blue_bin{8};
    std::uint8_t red_bin{8};
    Player side_to_move{Player::Blue};

    [[nodiscard]] friend constexpr bool operator==(
        const Position&, const Position&) = default;

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

[[nodiscard]] Position make_position(const GameState& state) {
    if (state.rules.edge != EdgeRule::Torus ||
        state.rules.all_on_board != AllOnBoardRule::Continue ||
        state.rules.move_when != MoveWhenRule::AllOnBoard ||
        state.rules.move_how != MoveHowRule::King ||
        state.rules.zero_move_allowed || state.rules.jumps_allowed) {
        throw std::invalid_argument(
            "AlphaBetaBot supports Torus + Continue + Move When All On Board + King");
    }

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

struct Geometry {
    std::array<std::array<std::uint8_t, 8>, 64> adjacent{};
    std::array<std::array<std::uint8_t, 8>, 64> destination{};
    std::array<std::array<std::uint8_t, 8>, 64> king_targets{};
    std::array<std::uint8_t, 64> king_count{};
    std::array<std::array<std::uint8_t, 64>, 512> maps{};
    std::array<std::array<std::uint8_t, 64>, 512> inverse_maps{};

    Geometry() {
        static constexpr std::array<std::array<int, 2>, 8> directions{{
            {{-1, -1}}, {{-1, 0}}, {{-1, 1}}, {{0, -1}},
            {{0, 1}}, {{1, -1}}, {{1, 0}}, {{1, 1}},
        }};

        for (int row = 0; row < 8; ++row) {
            for (int column = 0; column < 8; ++column) {
                const std::uint8_t center = GameState::square(row, column);
                for (std::size_t index = 0; index < directions.size(); ++index) {
                    const int dr = directions[index][0];
                    const int dc = directions[index][1];
                    adjacent[center][index] = GameState::square(
                        (row + dr + 8) % 8, (column + dc + 8) % 8);
                    destination[center][index] = GameState::square(
                        (row + 2 * dr + 16) % 8,
                        (column + 2 * dc + 16) % 8);

                    const int king_row = row + dr;
                    const int king_column = column + dc;
                    if (king_row >= 0 && king_row < 8 &&
                        king_column >= 0 && king_column < 8) {
                        king_targets[center][king_count[center]++] =
                            GameState::square(king_row, king_column);
                    }
                }
            }
        }

        for (int transform = 0; transform < 8; ++transform) {
            for (int row_shift = 0; row_shift < 8; ++row_shift) {
                for (int column_shift = 0; column_shift < 8; ++column_shift) {
                    const std::size_t map_index = static_cast<std::size_t>(
                        transform * 64 + row_shift * 8 + column_shift);
                    for (int row = 0; row < 8; ++row) {
                        for (int column = 0; column < 8; ++column) {
                            auto [new_row, new_column] =
                                transform_square(transform, row, column);
                            new_row = (new_row + row_shift) % 8;
                            new_column = (new_column + column_shift) % 8;
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

    [[nodiscard]] static constexpr std::pair<int, int> transform_square(
        int transform, int row, int column) noexcept {
        constexpr int last = 7;
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
    const std::array<std::uint8_t, 64>& map) noexcept {
    std::uint64_t transformed = 0;
    while (bits != 0) {
        const unsigned square = std::countr_zero(bits);
        transformed |= std::uint64_t{1} << map[square];
        bits &= bits - 1;
    }
    return transformed;
}

[[nodiscard]] std::uint64_t torus_shift(
    std::uint64_t bits, int delta_row, int delta_column) noexcept {
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
    const int rows = ((delta_row % 8) + 8) % 8;
    return std::rotl(bits, rows * 8);
}

[[nodiscard]] bool has_line(std::uint64_t pieces) noexcept {
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
        if (size == moves.size()) {
            throw std::overflow_error("strong move buffer capacity exceeded");
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
        for (std::uint8_t index = 0;
             index < geometry.king_count[source]; ++index) {
            const std::uint8_t target = geometry.king_targets[source][index];
            if ((occupied & (std::uint64_t{1} << target)) == 0) {
                result.push({static_cast<std::uint8_t>(source), target});
            }
        }
        movers &= movers - 1;
    }
    return result;
}

[[nodiscard]] Position apply_move(const Position& position,
                                  FastMove move) noexcept {
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
    const std::uint64_t occupied = snapshot_blue | snapshot_red;
    const Geometry& geometry = Geometry::instance();
    std::uint64_t clear = 0;
    std::uint64_t add_blue = 0;
    std::uint64_t add_red = 0;

    for (std::size_t index = 0; index < 8; ++index) {
        const std::uint8_t source = geometry.adjacent[move.to][index];
        const std::uint8_t target = geometry.destination[move.to][index];
        const std::uint64_t source_bit = std::uint64_t{1} << source;
        const std::uint64_t target_bit = std::uint64_t{1} << target;
        if ((occupied & source_bit) == 0 || (occupied & target_bit) != 0) {
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

[[nodiscard]] Outcome terminal_outcome(const Position& position) noexcept {
    const bool blue_line = has_line(position.blue);
    const bool red_line = has_line(position.red);
    if (blue_line && red_line) return Outcome::Draw;
    if (blue_line) return Outcome::BlueWin;
    if (red_line) return Outcome::RedWin;

    if (position.bin_count(position.side_to_move) != 0) {
        return Outcome::Ongoing;
    }

    const Geometry& geometry = Geometry::instance();
    const std::uint64_t occupied = position.occupied();
    std::uint64_t movers = position.pieces(position.side_to_move);
    while (movers != 0) {
        const unsigned source = std::countr_zero(movers);
        for (std::uint8_t index = 0;
             index < geometry.king_count[source]; ++index) {
            const std::uint8_t target = geometry.king_targets[source][index];
            if ((occupied & (std::uint64_t{1} << target)) == 0) {
                return Outcome::Ongoing;
            }
        }
        movers &= movers - 1;
    }
    return Outcome::Draw;
}

[[nodiscard]] int terminal_score(const Position& position) noexcept {
    const Outcome outcome = terminal_outcome(position);
    if (outcome == Outcome::Ongoing) return infinity;
    if (outcome == Outcome::Draw) return 0;
    const Player winner =
        outcome == Outcome::BlueWin ? Player::Blue : Player::Red;
    return winner == position.side_to_move ? mate_score : -mate_score;
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

[[nodiscard]] int adjacent_pair_count(std::uint64_t pieces) noexcept {
    static constexpr std::array<std::array<int, 2>, 4> directions{{
        {{0, 1}}, {{1, 0}}, {{1, 1}}, {{1, -1}},
    }};
    int count = 0;
    for (const auto& direction : directions) {
        count += std::popcount(
            pieces & torus_shift(pieces, direction[0], direction[1]));
    }
    return count;
}

[[nodiscard]] int immediate_win_count(Position position,
                                      Player player,
                                      int limit = 2) noexcept {
    position.side_to_move = player;
    const MoveList moves = generate_moves(position);
    int wins = 0;
    for (std::size_t index = 0; index < moves.size; ++index) {
        const Position child = apply_move(position, moves.moves[index]);
        const Outcome outcome = terminal_outcome(child);
        if ((player == Player::Blue && outcome == Outcome::BlueWin) ||
            (player == Player::Red && outcome == Outcome::RedWin)) {
            if (++wins == limit) break;
        }
    }
    return wins;
}

struct CanonicalKey {
    std::uint64_t ours{0};
    std::uint64_t theirs{0};
    std::uint8_t our_bin{0};
    std::uint8_t their_bin{0};

    [[nodiscard]] friend constexpr bool operator==(
        const CanonicalKey&, const CanonicalKey&) = default;
};

struct CanonicalForm {
    CanonicalKey key;
    std::uint16_t map_index{0};
};

[[nodiscard]] bool canonical_better(const CanonicalKey& candidate,
                                    const CanonicalKey& current) noexcept {
    const std::uint64_t candidate_occupied =
        candidate.ours | candidate.theirs;
    const std::uint64_t current_occupied = current.ours | current.theirs;
    if (candidate_occupied != current_occupied) {
        return candidate_occupied > current_occupied;
    }
    if (candidate.ours != current.ours) return candidate.ours > current.ours;
    return candidate.theirs > current.theirs;
}

class Canonicalizer {
public:
    [[nodiscard]] CanonicalForm operator()(
        const Position& position) const noexcept {
        const std::uint64_t ours = position.pieces(position.side_to_move);
        const std::uint64_t theirs = position.pieces(opponent(position.side_to_move));
        const std::uint8_t our_bin = position.bin_count(position.side_to_move);
        const std::uint8_t their_bin =
            position.bin_count(opponent(position.side_to_move));
        const std::uint64_t occupied = ours | theirs;
        if (occupied == 0) {
            return {{0, 0, our_bin, their_bin}, 0};
        }

        const Geometry& geometry = Geometry::instance();
        CanonicalForm best{};
        bool have_best = false;
        for (int transform = 0; transform < 8; ++transform) {
            std::uint64_t anchors = occupied;
            while (anchors != 0) {
                const unsigned source = std::countr_zero(anchors);
                const int row = static_cast<int>(source) / 8;
                const int column = static_cast<int>(source) % 8;
                const auto [transformed_row, transformed_column] =
                    Geometry::transform_square(transform, row, column);
                const int row_shift = (7 - transformed_row + 8) % 8;
                const int column_shift = (7 - transformed_column + 8) % 8;
                const std::uint16_t map_index = static_cast<std::uint16_t>(
                    transform * 64 + row_shift * 8 + column_shift);
                CanonicalKey candidate{
                    transform_bits(ours, geometry.maps[map_index]),
                    transform_bits(theirs, geometry.maps[map_index]),
                    our_bin,
                    their_bin,
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

    [[nodiscard]] FastMove to_canonical(
        FastMove move, std::uint16_t map_index) const noexcept {
        const auto& map = Geometry::instance().maps[map_index];
        return {
            move.from == no_square ? no_square : map[move.from],
            map[move.to],
        };
    }

    [[nodiscard]] FastMove from_canonical(
        FastMove move, std::uint16_t map_index) const noexcept {
        const auto& map = Geometry::instance().inverse_maps[map_index];
        return {
            move.from == no_square ? no_square : map[move.from],
            map[move.to],
        };
    }
};

[[nodiscard]] std::uint64_t mix64(std::uint64_t value) noexcept {
    value += 0x9E3779B97F4A7C15ULL;
    value = (value ^ (value >> 30U)) * 0xBF58476D1CE4E5B9ULL;
    value = (value ^ (value >> 27U)) * 0x94D049BB133111EBULL;
    return value ^ (value >> 31U);
}

[[nodiscard]] std::uint64_t hash_key(const CanonicalKey& key) noexcept {
    std::uint64_t hash = mix64(key.ours);
    hash ^= std::rotl(mix64(key.theirs), 21);
    const std::uint64_t bins = static_cast<std::uint64_t>(key.our_bin) |
        (static_cast<std::uint64_t>(key.their_bin) << 8U);
    return hash ^ std::rotl(mix64(bins), 43);
}

enum class Bound : std::uint8_t { Empty = 0, Exact, Lower, Upper };

struct TTEntry {
    std::uint64_t ours{0};
    std::uint64_t theirs{0};
    std::int32_t score{0};
    std::uint16_t best_move{no_move};
    std::uint16_t generation{0};
    std::uint8_t depth{0};
    std::uint8_t our_bin{0};
    std::uint8_t their_bin{0};
    Bound bound{Bound::Empty};
};

class TranspositionTable {
public:
    explicit TranspositionTable(std::size_t megabytes) {
        if (megabytes == 0) {
            throw std::invalid_argument("transposition table size must be non-zero");
        }
        const std::size_t bytes = megabytes * 1024ULL * 1024ULL;
        std::size_t count = 1;
        while (count <= bytes / sizeof(TTEntry) / 2U) count *= 2U;
        entries_.resize(count);
        mask_ = count - 1U;
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
        entry.ours = key.ours;
        entry.theirs = key.theirs;
        entry.our_bin = key.our_bin;
        entry.their_bin = key.their_bin;
        entry.score = score;
        entry.best_move = best_move;
        entry.generation = generation_;
        entry.depth = depth;
        entry.bound = bound;
    }

    [[nodiscard]] std::size_t bytes() const noexcept {
        return entries_.size() * sizeof(TTEntry);
    }

private:
    [[nodiscard]] static bool matches(const TTEntry& entry,
                                      const CanonicalKey& key) noexcept {
        return entry.bound != Bound::Empty &&
            entry.ours == key.ours && entry.theirs == key.theirs &&
            entry.our_bin == key.our_bin && entry.their_bin == key.their_bin;
    }

    std::vector<TTEntry> entries_;
    std::size_t mask_{0};
    std::uint16_t generation_{1};
};

struct AlphaBetaConfig {
    std::uint32_t time_limit_ms{1'000};
    std::uint8_t max_depth{64};
    std::size_t transposition_megabytes{64};
    std::uint64_t node_limit{0};
};

struct AlphaBetaStats {
    std::uint64_t nodes{0};
    std::uint64_t tt_hits{0};
    std::uint64_t tt_cutoffs{0};
    std::uint64_t beta_cutoffs{0};
    std::uint64_t root_symmetry_skips{0};
    std::uint64_t root_unsafe_moves{0};
};

struct AlphaBetaResult {
    Move move{};
    int score{0};
    std::uint8_t completed_depth{0};
    double seconds{0.0};
    AlphaBetaStats stats{};
    std::vector<Move> principal_variation;
};

struct SearchValue {
    int score{0};
    bool complete{true};
};

struct Candidate {
    FastMove move{};
    Position child{};
    int order{0};
};

class AlphaBetaBot {
public:
    explicit AlphaBetaBot(AlphaBetaConfig config = {})
        : config_(config), table_(config.transposition_megabytes) {
        if (config_.time_limit_ms == 0 || config_.max_depth == 0) {
            throw std::invalid_argument("alpha-beta limits must be non-zero");
        }
        history_.fill(0);
        for (auto& pair : killers_) pair.fill(no_move);
    }

    [[nodiscard]] std::optional<AlphaBetaResult> search(
        const GameState& game_state) {
        const Position root = make_position(game_state);
        if (terminal_outcome(root) != Outcome::Ongoing) return std::nullopt;

        const auto start = std::chrono::steady_clock::now();
        deadline_ = start + std::chrono::milliseconds(config_.time_limit_ms);
        stats_ = {};
        stopped_ = false;
        table_.new_generation();
        path_[0] = root;

        std::vector<Candidate> root_moves = make_root_candidates(root);
        if (root_moves.empty()) return std::nullopt;

        for (const Candidate& candidate : root_moves) {
            const Outcome outcome = terminal_outcome(candidate.child);
            const Player mover = root.side_to_move;
            if ((mover == Player::Blue && outcome == Outcome::BlueWin) ||
                (mover == Player::Red && outcome == Outcome::RedWin)) {
                AlphaBetaResult result;
                result.move = to_game_move(candidate.move);
                result.score = mate_score;
                result.seconds = std::chrono::duration<double>(
                    std::chrono::steady_clock::now() - start).count();
                result.stats = stats_;
                result.principal_variation.push_back(result.move);
                return result;
            }
        }

        filter_root_blunders(root, root_moves);
        FastMove best_move = root_moves.front().move;
        FastMove preferred = best_move;
        int best_score = evaluate(root_moves.front().child) * -1;
        std::uint8_t completed_depth = 0;

        for (std::uint8_t depth = 1; depth <= config_.max_depth; ++depth) {
            const RootIteration iteration =
                search_root(root, root_moves, depth, preferred);
            if (!iteration.complete) break;
            best_move = iteration.move;
            preferred = iteration.move;
            best_score = iteration.score;
            completed_depth = depth;
            if (std::abs(best_score) == mate_score) break;
        }

        AlphaBetaResult result;
        result.move = to_game_move(best_move);
        result.score = best_score;
        result.completed_depth = completed_depth;
        result.seconds = std::chrono::duration<double>(
            std::chrono::steady_clock::now() - start).count();
        result.stats = stats_;
        result.principal_variation = extract_pv(
            root, completed_depth == 0 ? 1 : completed_depth, best_move);
        return result;
    }

    [[nodiscard]] std::size_t table_bytes() const noexcept {
        return table_.bytes();
    }

private:
    struct RootIteration {
        FastMove move{};
        int score{0};
        bool complete{true};
    };

    [[nodiscard]] bool should_stop() noexcept {
        if (stopped_) return true;
        if (config_.node_limit != 0 && stats_.nodes >= config_.node_limit) {
            stopped_ = true;
            return true;
        }
        if ((stats_.nodes & 1023ULL) == 0 &&
            std::chrono::steady_clock::now() >= deadline_) {
            stopped_ = true;
        }
        return stopped_;
    }

    [[nodiscard]] int evaluate(const Position& position) const noexcept {
        const Player us = position.side_to_move;
        const Player them = opponent(us);
        const int our_wins = immediate_win_count(position, us, 2);
        if (our_wins != 0) return 180'000 + 20'000 * our_wins;
        const int their_wins = immediate_win_count(position, them, 2);
        if (their_wins != 0) return -150'000 - 25'000 * their_wins;

        const std::uint64_t occupied = position.occupied();
        const std::uint64_t ours = position.pieces(us);
        const std::uint64_t theirs = position.pieces(them);
        int score = 96 * (open_two_count(ours, occupied) -
                          open_two_count(theirs, occupied));
        score += 12 * (adjacent_pair_count(ours) -
                       adjacent_pair_count(theirs));
        score += 2 * (std::popcount(ours) - std::popcount(theirs));
        return score;
    }

    [[nodiscard]] int move_order(const Position& parent,
                                 FastMove move,
                                 const Position& child,
                                 std::uint16_t tt_move,
                                 std::uint8_t ply) const noexcept {
        int order = history_[encode_move(move)];
        if (encode_move(move) == tt_move) order += 1'000'000'000;
        if (ply < killers_.size()) {
            if (encode_move(move) == killers_[ply][0]) order += 100'000'000;
            if (encode_move(move) == killers_[ply][1]) order += 90'000'000;
        }

        const Outcome outcome = terminal_outcome(child);
        const Player mover = parent.side_to_move;
        if ((mover == Player::Blue && outcome == Outcome::BlueWin) ||
            (mover == Player::Red && outcome == Outcome::RedWin)) {
            return order + 800'000'000;
        }
        if (outcome == Outcome::Draw) order += 20'000'000;

        const std::uint64_t occupied = child.occupied();
        order += 512 * (
            open_two_count(child.pieces(mover), occupied) -
            open_two_count(child.pieces(opponent(mover)), occupied));
        order += 32 * (
            adjacent_pair_count(child.pieces(mover)) -
            adjacent_pair_count(child.pieces(opponent(mover))));
        return order;
    }

    [[nodiscard]] std::vector<Candidate> make_root_candidates(
        const Position& root) {
        const MoveList legal = generate_moves(root);
        std::vector<Candidate> candidates;
        candidates.reserve(legal.size);
        std::vector<CanonicalKey> seen;
        seen.reserve(legal.size);

        for (std::size_t index = 0; index < legal.size; ++index) {
            const FastMove move = legal.moves[index];
            const Position child = apply_move(root, move);
            const CanonicalKey key = canonicalize_(child).key;
            if (std::find(seen.begin(), seen.end(), key) != seen.end()) {
                ++stats_.root_symmetry_skips;
                continue;
            }
            seen.push_back(key);
            candidates.push_back({
                move,
                child,
                move_order(root, move, child, no_move, 0),
            });
        }
        return candidates;
    }

    void filter_root_blunders(const Position& root,
                              std::vector<Candidate>& candidates) {
        const Player opponent_player = opponent(root.side_to_move);
        std::vector<int> losing_replies(candidates.size(), 0);
        bool have_safe = false;
        for (std::size_t index = 0; index < candidates.size(); ++index) {
            losing_replies[index] = immediate_win_count(
                candidates[index].child, opponent_player,
                std::numeric_limits<int>::max());
            have_safe |= losing_replies[index] == 0;
        }

        if (have_safe) {
            std::vector<Candidate> safe;
            safe.reserve(candidates.size());
            for (std::size_t index = 0; index < candidates.size(); ++index) {
                if (losing_replies[index] == 0) {
                    safe.push_back(candidates[index]);
                } else {
                    ++stats_.root_unsafe_moves;
                }
            }
            candidates = std::move(safe);
        } else {
            for (std::size_t index = 0; index < candidates.size(); ++index) {
                candidates[index].order -= 1'000'000 * losing_replies[index];
            }
        }
        std::sort(candidates.begin(), candidates.end(),
                  [](const Candidate& left, const Candidate& right) {
                      return left.order > right.order;
                  });
    }

    [[nodiscard]] RootIteration search_root(
        const Position& root,
        std::vector<Candidate>& candidates,
        std::uint8_t depth,
        FastMove preferred) {
        for (Candidate& candidate : candidates) {
            if (candidate.move == preferred) candidate.order += 500'000'000;
        }
        std::stable_sort(candidates.begin(), candidates.end(),
                         [](const Candidate& left, const Candidate& right) {
                             return left.order > right.order;
                         });

        int alpha = -infinity;
        int best = -infinity;
        FastMove best_move = candidates.front().move;
        for (Candidate& candidate : candidates) {
            if (should_stop()) return {best_move, best, false};
            path_[0] = root;
            const SearchValue child = negamax(
                candidate.child, static_cast<std::uint8_t>(depth - 1),
                -infinity, -alpha, 1);
            if (!child.complete) return {best_move, best, false};
            const int score = -child.score;
            candidate.order = score;
            if (score > best) {
                best = score;
                best_move = candidate.move;
            }
            alpha = std::max(alpha, score);
        }

        const CanonicalForm canonical = canonicalize_(root);
        table_.store(canonical.key, depth, best, Bound::Exact,
                     encode_move(canonicalize_.to_canonical(
                         best_move, canonical.map_index)));
        return {best_move, best, true};
    }

    [[nodiscard]] SearchValue negamax(const Position& position,
                                      std::uint8_t depth,
                                      int alpha,
                                      int beta,
                                      std::uint8_t ply) {
        if (should_stop()) return {0, false};
        ++stats_.nodes;

        const int terminal = terminal_score(position);
        if (terminal != infinity) return {terminal, true};
        for (std::uint8_t index = 0; index < ply; ++index) {
            if (path_[index] == position) return {0, true};
        }
        if (depth == 0) return {evaluate(position), true};
        if (ply < path_.size()) path_[ply] = position;

        const bool allow_tt = position.blue_bin != 0 && position.red_bin != 0;
        CanonicalForm canonical{};
        const TTEntry* entry = nullptr;
        FastMove tt_move{};
        std::uint16_t encoded_tt_move = no_move;
        if (allow_tt) {
            canonical = canonicalize_(position);
            entry = table_.find(canonical.key);
            if (entry != nullptr) {
                ++stats_.tt_hits;
                if (entry->best_move != no_move) {
                    tt_move = canonicalize_.from_canonical(
                        decode_move(entry->best_move), canonical.map_index);
                    encoded_tt_move = encode_move(tt_move);
                }
                if (entry->depth >= depth) {
                    if (entry->bound == Bound::Exact ||
                        (entry->bound == Bound::Lower && entry->score >= beta) ||
                        (entry->bound == Bound::Upper && entry->score <= alpha)) {
                        ++stats_.tt_cutoffs;
                        return {entry->score, true};
                    }
                }
            }
        }

        const int original_alpha = alpha;
        const MoveList legal = generate_moves(position);
        if (legal.size == 0) return {0, true};
        std::array<Candidate, 128> candidates{};
        for (std::size_t index = 0; index < legal.size; ++index) {
            const FastMove move = legal.moves[index];
            const Position child = apply_move(position, move);
            candidates[index] = {
                move,
                child,
                move_order(position, move, child, encoded_tt_move, ply),
            };
        }
        std::sort(candidates.begin(),
                  candidates.begin() + static_cast<std::ptrdiff_t>(legal.size),
                  [](const Candidate& left, const Candidate& right) {
                      return left.order > right.order;
                  });

        int best = -infinity;
        FastMove best_move = candidates.front().move;
        bool cutoff = false;
        for (std::size_t index = 0; index < legal.size; ++index) {
            const SearchValue child = negamax(
                candidates[index].child,
                static_cast<std::uint8_t>(depth - 1),
                -beta,
                -alpha,
                static_cast<std::uint8_t>(ply + 1));
            if (!child.complete) return {0, false};
            const int score = -child.score;
            if (score > best) {
                best = score;
                best_move = candidates[index].move;
            }
            alpha = std::max(alpha, score);
            if (alpha >= beta) {
                cutoff = true;
                ++stats_.beta_cutoffs;
                const std::uint16_t encoded = encode_move(best_move);
                const int bonus = static_cast<int>(depth) *
                                  static_cast<int>(depth);
                history_[encoded] = std::min(
                    history_[encoded] + bonus, 10'000'000);
                if (ply < killers_.size() && killers_[ply][0] != encoded) {
                    killers_[ply][1] = killers_[ply][0];
                    killers_[ply][0] = encoded;
                }
                break;
            }
        }

        if (allow_tt) {
            Bound bound = Bound::Exact;
            if (best <= original_alpha) bound = Bound::Upper;
            if (cutoff || best >= beta) bound = Bound::Lower;
            table_.store(canonical.key, depth, best, bound,
                         encode_move(canonicalize_.to_canonical(
                             best_move, canonical.map_index)));
        }
        return {best, true};
    }

    [[nodiscard]] std::vector<Move> extract_pv(Position position,
                                               std::uint8_t depth,
                                               FastMove root_move) const {
        std::vector<Move> pv;
        pv.reserve(depth);
        pv.push_back(to_game_move(root_move));
        position = apply_move(position, root_move);
        for (std::uint8_t ply = 1; ply < depth; ++ply) {
            if (terminal_outcome(position) != Outcome::Ongoing ||
                position.blue_bin == 0 || position.red_bin == 0) {
                break;
            }
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
            pv.push_back(to_game_move(move));
            position = apply_move(position, move);
        }
        return pv;
    }

    AlphaBetaConfig config_;
    Canonicalizer canonicalize_;
    TranspositionTable table_;
    AlphaBetaStats stats_{};
    bool stopped_{false};
    std::chrono::steady_clock::time_point deadline_{};
    std::array<int, 4160> history_{};
    std::array<std::array<std::uint16_t, 2>, 128> killers_{};
    std::array<Position, 128> path_{};
};

} // namespace pop_tac_toe::strong

#ifdef POP_TAC_TOE_STRONG_STANDALONE
#include <charconv>
#include <iomanip>
#include <iostream>
#include <string_view>

namespace {

template <typename Integer>
bool parse_integer(std::string_view text, Integer& value) {
    const auto result =
        std::from_chars(text.data(), text.data() + text.size(), value);
    return result.ec == std::errc{} && result.ptr == text.data() + text.size();
}

std::string move_text(pop_tac_toe::Move move) {
    using pop_tac_toe::GameState;
    if (move.kind == pop_tac_toe::MoveKind::PlaceFromBin) {
        return "P(" + std::to_string(GameState::row_of(move.to)) + "," +
               std::to_string(GameState::column_of(move.to)) + ")";
    }
    return "T(" + std::to_string(GameState::row_of(move.from)) + "," +
           std::to_string(GameState::column_of(move.from)) + ")->(" +
           std::to_string(GameState::row_of(move.to)) + "," +
           std::to_string(GameState::column_of(move.to)) + ")";
}

} // namespace

int main(int argc, char** argv) {
    using namespace pop_tac_toe;
    using namespace pop_tac_toe::strong;

    std::uint32_t milliseconds = 1'000;
    std::uint32_t checkers = 8;
    std::uint32_t table_megabytes = 64;
    if ((argc > 1 && (!parse_integer(argv[1], milliseconds) || milliseconds == 0)) ||
        (argc > 2 && (!parse_integer(argv[2], checkers) ||
                      checkers < 3 || checkers > 16)) ||
        (argc > 3 && (!parse_integer(argv[3], table_megabytes) ||
                      table_megabytes == 0)) ||
        argc > 4) {
        std::cerr << "Usage: " << argv[0]
                  << " [milliseconds] [checkers:3-16] [tt-megabytes]\n";
        return 2;
    }

    RuleConfig rules = RuleConfig::computer_torus();
    rules.blue_checkers = static_cast<std::uint8_t>(checkers);
    rules.red_checkers = static_cast<std::uint8_t>(checkers);
    GameState state(rules);
    AlphaBetaConfig config;
    config.time_limit_ms = milliseconds;
    config.transposition_megabytes = table_megabytes;
    AlphaBetaBot bot(config);
    const std::optional<AlphaBetaResult> result = bot.search(state);
    if (!result) {
        std::cerr << "No legal move.\n";
        return 1;
    }

    std::cout << "move=" << move_text(result->move)
              << " score=" << result->score
              << " depth=" << static_cast<unsigned>(result->completed_depth)
              << " nodes=" << result->stats.nodes
              << " tt_hits=" << result->stats.tt_hits
              << " tt_cutoffs=" << result->stats.tt_cutoffs
              << " beta_cutoffs=" << result->stats.beta_cutoffs
              << " root_symmetry_skips=" << result->stats.root_symmetry_skips
              << " root_unsafe_moves=" << result->stats.root_unsafe_moves
              << " seconds=" << std::fixed << std::setprecision(6)
              << result->seconds
              << " nodes_per_second="
              << (result->seconds > 0.0
                      ? static_cast<double>(result->stats.nodes) / result->seconds
                      : 0.0)
              << '\n';
    std::cout << "pv=";
    for (std::size_t index = 0;
         index < result->principal_variation.size(); ++index) {
        if (index != 0) std::cout << ' ';
        std::cout << move_text(result->principal_variation[index]);
    }
    std::cout << '\n';
    return 0;
}
#endif
