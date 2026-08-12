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
#include <limits>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

namespace pop_tac_toe::strategy {

constexpr int board_width = 8;
constexpr int board_height = 8;
constexpr int board_squares = 64;
constexpr std::uint8_t no_square = 64;
constexpr std::uint32_t no_parent = std::numeric_limits<std::uint32_t>::max();

enum class Player : std::uint8_t { Blue, Red };
enum class Outcome : std::uint8_t { Ongoing, BlueWin, RedWin, Draw };

[[nodiscard]] constexpr Player opponent(Player player) noexcept {
    return player == Player::Blue ? Player::Red : Player::Blue;
}

struct Move {
    std::uint8_t from{no_square};
    std::uint8_t to{0};

    [[nodiscard]] friend constexpr bool operator==(const Move&,
                                                    const Move&) = default;
};

struct Position {
    std::uint64_t blue{0};
    std::uint64_t red{0};
    std::uint8_t blue_bin{8};
    std::uint8_t red_bin{8};
    Player side_to_move{Player::Blue};

    [[nodiscard]] constexpr std::uint64_t occupied() const noexcept {
        return blue | red;
    }

    [[nodiscard]] constexpr std::uint64_t pieces(Player player) const noexcept {
        return player == Player::Blue ? blue : red;
    }

    [[nodiscard]] constexpr std::uint8_t bin(Player player) const noexcept {
        return player == Player::Blue ? blue_bin : red_bin;
    }
};

struct PositionKey {
    std::uint64_t blue{0};
    std::uint64_t red{0};
    std::uint8_t blue_bin{0};
    std::uint8_t red_bin{0};
    Player side_to_move{Player::Blue};

    [[nodiscard]] friend constexpr bool operator==(const PositionKey&,
                                                    const PositionKey&) = default;
};

[[nodiscard]] std::uint64_t mix64(std::uint64_t value) noexcept {
    value += 0x9E3779B97F4A7C15ULL;
    value = (value ^ (value >> 30U)) * 0xBF58476D1CE4E5B9ULL;
    value = (value ^ (value >> 27U)) * 0x94D049BB133111EBULL;
    return value ^ (value >> 31U);
}

struct PositionKeyHash {
    [[nodiscard]] std::size_t operator()(const PositionKey& key) const noexcept {
        std::uint64_t hash = mix64(key.blue);
        hash ^= std::rotl(mix64(key.red), 21);
        hash ^= std::rotl(mix64(static_cast<std::uint64_t>(key.blue_bin) |
                               (static_cast<std::uint64_t>(key.red_bin) << 8U) |
                               (static_cast<std::uint64_t>(key.side_to_move) << 16U)),
                          43);
        return static_cast<std::size_t>(hash);
    }
};

[[nodiscard]] constexpr PositionKey key_of(const Position& position) noexcept {
    return {position.blue, position.red,
            position.blue_bin, position.red_bin, position.side_to_move};
}

struct MoveList {
    std::array<Move, 128> moves{};
    std::uint16_t size{0};

    void push(Move move) noexcept { moves[size++] = move; }
};

struct Geometry {
    std::array<std::array<std::uint8_t, 8>, board_squares> adjacent{};
    std::array<std::array<std::uint8_t, 8>, board_squares> destination{};
    std::array<std::array<std::uint8_t, 8>, board_squares> king_targets{};
    std::array<std::uint8_t, board_squares> king_count{};

    Geometry() {
        static constexpr std::array<std::array<int, 2>, 8> directions{{
            {{-1, -1}}, {{-1, 0}}, {{-1, 1}}, {{0, -1}},
            {{0, 1}}, {{1, -1}}, {{1, 0}}, {{1, 1}},
        }};

        for (int row = 0; row < board_height; ++row) {
            for (int column = 0; column < board_width; ++column) {
                const auto center = square(row, column);
                for (std::size_t index = 0; index < directions.size(); ++index) {
                    const int delta_row = directions[index][0];
                    const int delta_column = directions[index][1];
                    adjacent[center][index] = square(
                        (row + delta_row + board_height) % board_height,
                        (column + delta_column + board_width) % board_width);
                    destination[center][index] = square(
                        (row + 2 * delta_row + 2 * board_height) % board_height,
                        (column + 2 * delta_column + 2 * board_width) % board_width);

                    const int target_row = row + delta_row;
                    const int target_column = column + delta_column;
                    if (in_bounds(target_row, target_column)) {
                        king_targets[center][king_count[center]++] =
                            square(target_row, target_column);
                    }
                }
            }
        }
    }

    [[nodiscard]] static constexpr bool in_bounds(int row,
                                                   int column) noexcept {
        return row >= 0 && row < board_height &&
               column >= 0 && column < board_width;
    }

    [[nodiscard]] static constexpr std::uint8_t square(int row,
                                                       int column) noexcept {
        return static_cast<std::uint8_t>(row * board_width + column);
    }

    [[nodiscard]] static const Geometry& instance() {
        static const Geometry geometry;
        return geometry;
    }
};

[[nodiscard]] std::uint64_t torus_shift(std::uint64_t bits,
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

    const int wrapped_rows =
        ((delta_row % board_height) + board_height) % board_height;
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

[[nodiscard]] MoveList generate_moves(const Position& position) noexcept {
    MoveList result;
    const std::uint64_t occupied = position.occupied();
    if (position.bin(position.side_to_move) != 0) {
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

[[nodiscard]] bool is_legal(const Position& position, Move move) noexcept {
    const MoveList legal = generate_moves(position);
    for (std::uint16_t index = 0; index < legal.size; ++index) {
        if (legal.moves[index] == move) return true;
    }
    return false;
}

[[nodiscard]] Position apply_move(const Position& position, Move move) noexcept {
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
    const bool blue_line = has_torus_line(position.blue);
    const bool red_line = has_torus_line(position.red);
    if (blue_line && red_line) return Outcome::Draw;
    if (blue_line) return Outcome::BlueWin;
    if (red_line) return Outcome::RedWin;
    return generate_moves(position).size == 0 ? Outcome::Draw
                                               : Outcome::Ongoing;
}

enum class SpatialKind : std::uint8_t {
    Identity,
    Rotate90,
    Rotate180,
    Rotate270,
    MirrorVertical,
    MirrorAntiDiagonal,
    MirrorHorizontal,
    MirrorMainDiagonal,
};

[[nodiscard]] constexpr std::pair<int, int> transform_coordinates(
    SpatialKind kind,
    int row,
    int column) noexcept {
    constexpr int last = board_width - 1;
    switch (kind) {
    case SpatialKind::Identity: return {row, column};
    case SpatialKind::Rotate90: return {column, last - row};
    case SpatialKind::Rotate180: return {last - row, last - column};
    case SpatialKind::Rotate270: return {last - column, row};
    case SpatialKind::MirrorVertical: return {row, last - column};
    case SpatialKind::MirrorAntiDiagonal: return {last - column, last - row};
    case SpatialKind::MirrorHorizontal: return {last - row, column};
    case SpatialKind::MirrorMainDiagonal: return {column, row};
    }
    return {row, column};
}

[[nodiscard]] constexpr std::string_view kind_name(SpatialKind kind) noexcept {
    switch (kind) {
    case SpatialKind::Identity: return "identity";
    case SpatialKind::Rotate90: return "rotate90";
    case SpatialKind::Rotate180: return "rotate180";
    case SpatialKind::Rotate270: return "rotate270";
    case SpatialKind::MirrorVertical: return "mirror_vertical";
    case SpatialKind::MirrorAntiDiagonal: return "mirror_anti_diagonal";
    case SpatialKind::MirrorHorizontal: return "mirror_horizontal";
    case SpatialKind::MirrorMainDiagonal: return "mirror_main_diagonal";
    }
    return "unknown";
}

struct Transform {
    SpatialKind kind{SpatialKind::Identity};
    std::uint8_t row_shift{0};
    std::uint8_t column_shift{0};
    std::array<std::uint8_t, board_squares> map{};
    bool travel_compatible{false};
};

[[nodiscard]] bool is_king_neighbor(std::uint8_t source,
                                    std::uint8_t target) noexcept {
    const int source_row = source / board_width;
    const int source_column = source % board_width;
    const int target_row = target / board_width;
    const int target_column = target % board_width;
    const int row_distance = std::abs(source_row - target_row);
    const int column_distance = std::abs(source_column - target_column);
    return std::max(row_distance, column_distance) == 1;
}

[[nodiscard]] bool preserves_king_graph(const Transform& transform) noexcept {
    for (std::uint8_t source = 0; source < board_squares; ++source) {
        for (std::uint8_t target = 0; target < board_squares; ++target) {
            if (is_king_neighbor(source, target) !=
                is_king_neighbor(transform.map[source], transform.map[target])) {
                return false;
            }
        }
    }
    return true;
}

[[nodiscard]] std::vector<Transform> candidate_transforms() {
    std::vector<Transform> candidates;
    for (int kind_value = 0; kind_value < 8; ++kind_value) {
        const auto kind = static_cast<SpatialKind>(kind_value);
        for (int row_shift = 0; row_shift < board_height; ++row_shift) {
            for (int column_shift = 0;
                 column_shift < board_width; ++column_shift) {
                Transform transform;
                transform.kind = kind;
                transform.row_shift = static_cast<std::uint8_t>(row_shift);
                transform.column_shift =
                    static_cast<std::uint8_t>(column_shift);
                for (int row = 0; row < board_height; ++row) {
                    for (int column = 0; column < board_width; ++column) {
                        auto [new_row, new_column] =
                            transform_coordinates(kind, row, column);
                        new_row = (new_row + row_shift) % board_height;
                        new_column = (new_column + column_shift) % board_width;
                        transform.map[Geometry::square(row, column)] =
                            Geometry::square(new_row, new_column);
                    }
                }

                bool involution = true;
                bool fixed_point_free = true;
                for (std::uint8_t square = 0;
                     square < board_squares; ++square) {
                    involution &=
                        transform.map[transform.map[square]] == square;
                    fixed_point_free &= transform.map[square] != square;
                }
                if (!involution || !fixed_point_free) continue;
                transform.travel_compatible = preserves_king_graph(transform);
                candidates.push_back(transform);
            }
        }
    }
    return candidates;
}

[[nodiscard]] Move transform_move(Move move,
                                  const Transform& transform) noexcept {
    return {
        move.from == no_square ? no_square : transform.map[move.from],
        transform.map[move.to],
    };
}

[[nodiscard]] std::string move_text(Move move) {
    const auto square_text = [](std::uint8_t square) {
        return std::string("(") +
            std::to_string(square / board_width) + "," +
            std::to_string(square % board_width) + ")";
    };
    if (move.from == no_square) return "P" + square_text(move.to);
    return "T" + square_text(move.from) + "->" + square_text(move.to);
}

[[nodiscard]] std::string transform_text(const Transform& transform) {
    return std::string(kind_name(transform.kind)) + "+shift(" +
        std::to_string(transform.row_shift) + "," +
        std::to_string(transform.column_shift) + ")";
}

enum class VerificationMode : std::uint8_t { Placement, Full };
enum class ResultKind : std::uint8_t { Refuted, Verified, Inconclusive };
enum class FailureReason : std::uint8_t {
    None,
    BlueWinAfterBlue,
    IllegalMappedReply,
    BlueWinAfterRed,
    StateLimit,
};

[[nodiscard]] constexpr std::string_view reason_text(
    FailureReason reason) noexcept {
    switch (reason) {
    case FailureReason::None: return "none";
    case FailureReason::BlueWinAfterBlue: return "blue_win_after_blue_move";
    case FailureReason::IllegalMappedReply: return "mapped_red_reply_illegal";
    case FailureReason::BlueWinAfterRed: return "blue_win_after_red_reply";
    case FailureReason::StateLimit: return "state_limit";
    }
    return "unknown";
}

struct TraceMove {
    Player player{Player::Blue};
    Move move{};
    bool legal{true};
};

struct SearchNode {
    Position position;
    std::uint32_t parent{no_parent};
    Move blue_move{};
    Move red_move{};
};

struct VerificationResult {
    ResultKind kind{ResultKind::Inconclusive};
    FailureReason reason{FailureReason::None};
    std::uint64_t states{0};
    std::uint64_t blue_edges{0};
    std::uint64_t repeated_states{0};
    std::uint32_t completed_blue_turns{0};
    double seconds{0.0};
    std::vector<TraceMove> trace;
};

[[nodiscard]] std::vector<TraceMove> reconstruct_trace(
    const std::vector<SearchNode>& nodes,
    std::uint32_t node_index,
    Move final_blue,
    std::optional<Move> final_red,
    bool final_red_legal) {
    std::vector<std::uint32_t> chain;
    for (std::uint32_t current = node_index;
         current != 0 && current != no_parent;
         current = nodes[current].parent) {
        chain.push_back(current);
    }
    std::reverse(chain.begin(), chain.end());

    std::vector<TraceMove> trace;
    trace.reserve(chain.size() * 2 + 2);
    for (const std::uint32_t index : chain) {
        trace.push_back({Player::Blue, nodes[index].blue_move, true});
        trace.push_back({Player::Red, nodes[index].red_move, true});
    }
    trace.push_back({Player::Blue, final_blue, true});
    if (final_red.has_value()) {
        trace.push_back({Player::Red, *final_red, final_red_legal});
    }
    return trace;
}

[[nodiscard]] VerificationResult verify_strategy(
    const Transform& transform,
    VerificationMode mode,
    std::uint8_t checkers,
    std::uint64_t max_states) {
    const auto start = std::chrono::steady_clock::now();
    VerificationResult result;
    std::vector<SearchNode> nodes;
    nodes.reserve(static_cast<std::size_t>(
        std::min<std::uint64_t>(max_states, 1'000'000)));
    nodes.push_back({Position{0, 0, checkers, checkers, Player::Blue},
                     no_parent, {}, {}});

    std::unordered_map<PositionKey, std::uint32_t, PositionKeyHash> seen;
    seen.reserve(static_cast<std::size_t>(
        std::min<std::uint64_t>(max_states, 1'000'000)));
    seen.emplace(key_of(nodes.front().position), 0);

    std::vector<std::uint32_t> frontier{0};
    std::uint32_t blue_turn = 0;

    const auto finish = [&](ResultKind kind, FailureReason reason) {
        result.kind = kind;
        result.reason = reason;
        result.states = nodes.size();
        result.completed_blue_turns = blue_turn;
        result.seconds = std::chrono::duration<double>(
            std::chrono::steady_clock::now() - start).count();
        return result;
    };

    while (!frontier.empty()) {
        if (mode == VerificationMode::Placement && blue_turn == checkers) {
            return finish(ResultKind::Verified, FailureReason::None);
        }

        std::vector<std::uint32_t> next_frontier;
        for (const std::uint32_t node_index : frontier) {
            const Position position = nodes[node_index].position;
            const MoveList blue_moves = generate_moves(position);
            for (std::uint16_t move_index = 0;
                 move_index < blue_moves.size; ++move_index) {
                ++result.blue_edges;
                const Move blue_move = blue_moves.moves[move_index];
                const Position after_blue = apply_move(position, blue_move);
                const Outcome after_blue_outcome = terminal_outcome(after_blue);
                if (after_blue_outcome == Outcome::BlueWin) {
                    result.trace = reconstruct_trace(
                        nodes, node_index, blue_move, std::nullopt, true);
                    return finish(ResultKind::Refuted,
                                  FailureReason::BlueWinAfterBlue);
                }
                if (after_blue_outcome != Outcome::Ongoing) continue;

                const Move red_move = transform_move(blue_move, transform);
                if (!is_legal(after_blue, red_move)) {
                    result.trace = reconstruct_trace(
                        nodes, node_index, blue_move, red_move, false);
                    return finish(ResultKind::Refuted,
                                  FailureReason::IllegalMappedReply);
                }

                const Position after_red = apply_move(after_blue, red_move);
                const Outcome after_red_outcome = terminal_outcome(after_red);
                if (after_red_outcome == Outcome::BlueWin) {
                    result.trace = reconstruct_trace(
                        nodes, node_index, blue_move, red_move, true);
                    return finish(ResultKind::Refuted,
                                  FailureReason::BlueWinAfterRed);
                }
                if (after_red_outcome != Outcome::Ongoing) continue;

                const PositionKey key = key_of(after_red);
                if (seen.contains(key)) {
                    ++result.repeated_states;
                    continue;
                }
                if (max_states != 0 && nodes.size() >= max_states) {
                    return finish(ResultKind::Inconclusive,
                                  FailureReason::StateLimit);
                }
                const auto child_index =
                    static_cast<std::uint32_t>(nodes.size());
                nodes.push_back({after_red, node_index, blue_move, red_move});
                seen.emplace(key, child_index);
                next_frontier.push_back(child_index);
            }
        }
        frontier = std::move(next_frontier);
        ++blue_turn;
    }

    return finish(ResultKind::Verified, FailureReason::None);
}

void print_trace(const std::vector<TraceMove>& trace) {
    std::cout << " counterexample=";
    for (std::size_t index = 0; index < trace.size(); ++index) {
        if (index != 0) std::cout << ' ';
        const TraceMove& item = trace[index];
        std::cout << (item.player == Player::Blue ? "B:" : "R:");
        if (!item.legal) std::cout << "ILLEGAL:";
        std::cout << move_text(item.move);
    }
}

[[nodiscard]] bool parse_u64(std::string_view input,
                             std::uint64_t& value) noexcept {
    const auto result = std::from_chars(
        input.data(), input.data() + input.size(), value);
    return result.ec == std::errc{} &&
           result.ptr == input.data() + input.size();
}

void print_usage(const char* program) {
    std::cerr
        << "Usage: " << program
        << " [placement|full] [checkers:3-16] [max-states-per-strategy]\n\n"
        << "placement tests all fixed-point-free involutive torus symmetries.\n"
        << "full tests only the subset that also preserves bounded King travel.\n"
        << "A REFUTED result includes a shortest counterexample for that policy.\n"
        << "VERIFIED in placement mode covers only the placement phase.\n";
}

} // namespace pop_tac_toe::strategy

int main(int argc, char** argv) {
    using namespace pop_tac_toe::strategy;

    VerificationMode mode = VerificationMode::Placement;
    std::uint64_t parsed_checkers = 8;
    std::uint64_t max_states = 5'000'000;

    if (argc > 1) {
        const std::string_view mode_text = argv[1];
        if (mode_text == "placement") {
            mode = VerificationMode::Placement;
        } else if (mode_text == "full") {
            mode = VerificationMode::Full;
        } else {
            print_usage(argv[0]);
            return 2;
        }
    }
    if ((argc > 2 && (!parse_u64(argv[2], parsed_checkers) ||
                      parsed_checkers < 3 || parsed_checkers > 16)) ||
        (argc > 3 && (!parse_u64(argv[3], max_states) || max_states == 0 ||
                      max_states >= no_parent)) ||
        argc > 4) {
        print_usage(argv[0]);
        return 2;
    }

    const auto checkers = static_cast<std::uint8_t>(parsed_checkers);
    const std::vector<Transform> all_candidates = candidate_transforms();
    std::vector<Transform> candidates;
    for (const Transform& transform : all_candidates) {
        if (mode == VerificationMode::Placement || transform.travel_compatible) {
            candidates.push_back(transform);
        }
    }

    std::cout << "rules=torus+continue+move_when_all_on_board+king"
              << " mode="
              << (mode == VerificationMode::Placement ? "placement" : "full")
              << " checkers_per_player=" << parsed_checkers
              << " candidate_strategies=" << candidates.size()
              << " max_states_per_strategy=" << max_states
              << " coordinates=zero_based\n";
    std::cout << "policy=red_maps_blue_previous_move_through_a_fixed_point_free_"
                 "involutive_symmetry repetition=draw\n";

    std::size_t refuted = 0;
    std::size_t verified = 0;
    std::size_t inconclusive = 0;
    for (const Transform& transform : candidates) {
        const VerificationResult result =
            verify_strategy(transform, mode, checkers, max_states);
        std::cout << "strategy=" << transform_text(transform)
                  << " travel_compatible="
                  << (transform.travel_compatible ? "yes" : "no");
        if (result.kind == ResultKind::Refuted) {
            ++refuted;
            std::cout << " result=REFUTED"
                      << " reason=" << reason_text(result.reason);
        } else if (result.kind == ResultKind::Verified) {
            ++verified;
            std::cout << " result=VERIFIED_NONLOSS"
                      << " scope="
                      << (mode == VerificationMode::Placement
                              ? "placement_phase_only"
                              : "full_reachable_graph");
        } else {
            ++inconclusive;
            std::cout << " result=INCONCLUSIVE"
                      << " reason=" << reason_text(result.reason);
        }
        std::cout << " completed_blue_turns=" << result.completed_blue_turns
                  << " states=" << result.states
                  << " blue_edges=" << result.blue_edges
                  << " repeated_states=" << result.repeated_states
                  << " seconds=" << std::fixed << std::setprecision(6)
                  << result.seconds;
        if (!result.trace.empty()) print_trace(result.trace);
        std::cout << '\n';
    }

    std::cout << "summary refuted=" << refuted
              << " verified=" << verified
              << " inconclusive=" << inconclusive << '\n';
    if (verified == 0 && inconclusive == 0) {
        std::cout << "conclusion=no_candidate_fixed_symmetry_strategy_survives"
                  << (mode == VerificationMode::Placement
                          ? "_the_placement_test\n"
                          : "_the_full_game_test\n");
    } else if (verified != 0) {
        std::cout << "conclusion=at_least_one_candidate_guarantees_red_nonloss_"
                  << (mode == VerificationMode::Placement
                          ? "during_placement_only\n"
                          : "for_the_full_game\n");
    } else {
        std::cout << "conclusion=inconclusive_due_to_resource_limit\n";
    }
    return inconclusive == 0 ? 0 : 3;
}
