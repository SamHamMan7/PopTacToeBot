#ifndef POP_TAC_TOE_MCTS_INCLUDED
#define POP_TAC_TOE_MCTS_INCLUDED

#include <algorithm>
#include <array>
#include <cassert>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <limits>
#include <optional>
#include <stdexcept>
#include <unordered_set>
#include <utility>
#include <vector>

#ifdef POP_TAC_TOE_STANDALONE
#include <charconv>
#include <chrono>
#include <iostream>
#include <string_view>
#endif

namespace pop_tac_toe {

enum class Player : std::uint8_t { None = 0, Blue = 1, Red = 2 };

[[nodiscard]] constexpr Player opponent(Player player) noexcept {
    return player == Player::Blue ? Player::Red : Player::Blue;
}

enum class EdgeRule : std::uint8_t { Reincarnation, Ringout, Blocked, Torus, Klein };
enum class AllOnBoardRule : std::uint8_t { Win, Continue };
enum class MoveWhenRule : std::uint8_t { Never, AllOnBoard, Always };
enum class MoveHowRule : std::uint8_t { King, Rook, Bishop, Queen, Anywhere };
enum class MoveKind : std::uint8_t { PlaceFromBin, MoveOnBoard };
enum class Outcome : std::uint8_t { Ongoing, BlueWin, RedWin, Draw };

struct RuleConfig {
    std::uint8_t blue_checkers{8};
    std::uint8_t red_checkers{8};
    EdgeRule edge{EdgeRule::Reincarnation};
    AllOnBoardRule all_on_board{AllOnBoardRule::Continue};
    MoveWhenRule move_when{MoveWhenRule::AllOnBoard};
    MoveHowRule move_how{MoveHowRule::King};
    bool zero_move_allowed{false};
    bool jumps_allowed{false};

    [[nodiscard]] static constexpr RuleConfig beginner() noexcept { return {}; }

    [[nodiscard]] static constexpr RuleConfig computer_torus() noexcept {
        RuleConfig config;
        config.edge = EdgeRule::Torus;
        return config;
    }

    void validate() const {
        if (blue_checkers < 3 || red_checkers < 3 ||
            blue_checkers > 16 || red_checkers > 16) {
            throw std::invalid_argument("Checker counts must be between 3 and 16 per player");
        }
    }
};

struct Move {
    static constexpr std::uint8_t no_square = 0xFF;

    MoveKind kind{MoveKind::PlaceFromBin};
    std::uint8_t from{no_square};
    std::uint8_t to{no_square};

    [[nodiscard]] friend constexpr bool operator==(const Move&, const Move&) = default;
};

struct GameState {
    static constexpr int width = 8;
    static constexpr int height = 8;
    static constexpr std::size_t board_size = width * height;

    std::vector<Player> board;
    std::vector<std::uint8_t> blue_bin;
    std::vector<std::uint8_t> red_bin;
    RuleConfig rules;
    Player next_player{Player::Blue};
    std::uint32_t ply{0};

    explicit GameState(RuleConfig config = RuleConfig::beginner())
        : board(board_size, Player::None), rules(config) {
        rules.validate();
        blue_bin.assign(rules.blue_checkers, 1);
        red_bin.assign(rules.red_checkers, 1);
        blue_bin.reserve(rules.blue_checkers);
        red_bin.reserve(rules.red_checkers);
    }

    [[nodiscard]] static constexpr std::uint8_t square(int row, int column) noexcept {
        return static_cast<std::uint8_t>(row * width + column);
    }

    [[nodiscard]] static constexpr int row_of(std::uint8_t sq) noexcept {
        return sq / width;
    }

    [[nodiscard]] static constexpr int column_of(std::uint8_t sq) noexcept {
        return sq % width;
    }

    [[nodiscard]] const std::vector<std::uint8_t>& bin(Player player) const {
        return player == Player::Blue ? blue_bin : red_bin;
    }

    [[nodiscard]] std::vector<std::uint8_t>& bin(Player player) {
        return player == Player::Blue ? blue_bin : red_bin;
    }

    [[nodiscard]] std::size_t on_board(Player player) const noexcept {
        return static_cast<std::size_t>(std::count(board.begin(), board.end(), player));
    }

    [[nodiscard]] std::size_t alive(Player player) const noexcept {
        return on_board(player) + bin(player).size();
    }

    [[nodiscard]] bool movement_allowed(Player player) const noexcept {
        switch (rules.move_when) {
        case MoveWhenRule::Never:
            return false;
        case MoveWhenRule::AllOnBoard:
            return bin(player).empty();
        case MoveWhenRule::Always:
            return true;
        }
        return false;
    }

    [[nodiscard]] std::vector<Move> get_legal_moves() const {
        std::vector<Move> moves;
        moves.reserve(512);

        if (!bin(next_player).empty()) {
            for (std::uint8_t to = 0; to < board_size; ++to) {
                if (board[to] == Player::None) {
                    moves.push_back({MoveKind::PlaceFromBin, Move::no_square, to});
                }
            }
        }

        if (!movement_allowed(next_player)) {
            return moves;
        }

        for (std::uint8_t from = 0; from < board_size; ++from) {
            if (board[from] != next_player) {
                continue;
            }
            append_moves_from(from, moves);
        }
        return moves;
    }

    void apply_move(const Move& move) {
        if (move.to >= board_size) {
            throw std::invalid_argument("Move target is outside the board");
        }

#ifndef NDEBUG
        const std::vector<Move> legal = get_legal_moves();
        if (std::find(legal.begin(), legal.end(), move) == legal.end()) {
            throw std::invalid_argument("Move is not legal in this position");
        }
#endif

        const Player mover = next_player;
        if (move.kind == MoveKind::PlaceFromBin) {
            if (bin(mover).empty() || board[move.to] != Player::None) {
                throw std::invalid_argument("Illegal placement");
            }
            bin(mover).pop_back();
        } else {
            if (!movement_allowed(mover) || move.from >= board_size ||
                board[move.from] != mover ||
                (move.from == move.to && !rules.zero_move_allowed) ||
                (move.from != move.to && board[move.to] != Player::None)) {
                throw std::invalid_argument("Illegal movement");
            }
            board[move.from] = Player::None;
        }

        board[move.to] = mover;
        apply_pop_mechanic(move.to);
        next_player = opponent(next_player);
        ++ply;
    }

    // Every push is selected from one post-placement snapshot, then committed.
    // This makes the result independent of direction iteration order.
    void apply_pop_mechanic(std::uint8_t center) {
        struct Push {
            std::uint8_t from;
            std::uint8_t to;
            Player piece;
            bool leaves_board;
            bool valid{true};
        };

        static constexpr std::array<std::array<int, 2>, 8> directions{{
            {{-1, -1}}, {{-1, 0}}, {{-1, 1}}, {{0, -1}},
            {{0, 1}}, {{1, -1}}, {{1, 0}}, {{1, 1}},
        }};

        std::array<Player, board_size> snapshot{};
        std::copy(board.begin(), board.end(), snapshot.begin());
        std::vector<Push> pushes;
        pushes.reserve(8);

        for (const auto& direction : directions) {
            Cursor cursor{row_of(center), column_of(center), direction[0], direction[1]};
            if (!advance(cursor)) {
                continue;
            }

            const std::uint8_t adjacent = square(cursor.row, cursor.column);
            const Player piece = snapshot[adjacent];
            if (piece == Player::None) {
                continue;
            }

            Cursor destination = cursor;
            if (!advance(destination)) {
                if (rules.edge == EdgeRule::Blocked) {
                    continue;
                }
                pushes.push_back({adjacent, Move::no_square, piece, true});
                continue;
            }

            const std::uint8_t target = square(destination.row, destination.column);
            if (snapshot[target] == Player::None) {
                pushes.push_back({adjacent, target, piece, false});
            }
        }

        std::array<std::uint8_t, board_size> claims{};
        for (const Push& push : pushes) {
            if (!push.leaves_board) {
                ++claims[push.to];
            }
        }
        for (Push& push : pushes) {
            if (!push.leaves_board && claims[push.to] != 1) {
                push.valid = false;
            }
        }

        for (const Push& push : pushes) {
            if (push.valid) {
                board[push.from] = Player::None;
            }
        }
        for (const Push& push : pushes) {
            if (!push.valid) {
                continue;
            }
            if (push.leaves_board) {
                if (rules.edge == EdgeRule::Reincarnation) {
                    bin(push.piece).push_back(1);
                }
            } else {
                board[push.to] = push.piece;
            }
        }
    }

    [[nodiscard]] Outcome outcome_before_mobility() const noexcept {
        const auto [blue_line, red_line] = line_winners();
        if (blue_line && red_line) return Outcome::Draw;
        if (blue_line) return Outcome::BlueWin;
        if (red_line) return Outcome::RedWin;

        if (rules.edge == EdgeRule::Ringout) {
            const bool blue_out = alive(Player::Blue) <= 2;
            const bool red_out = alive(Player::Red) <= 2;
            if (blue_out && red_out) return Outcome::Draw;
            if (blue_out) return Outcome::RedWin;
            if (red_out) return Outcome::BlueWin;
        }

        if (ply != 0) {
            const Player last_mover = opponent(next_player);
            if (bin(last_mover).empty()) {
                if (rules.all_on_board == AllOnBoardRule::Win) {
                    return last_mover == Player::Blue ? Outcome::BlueWin : Outcome::RedWin;
                }
                if (rules.move_when == MoveWhenRule::Never) {
                    return Outcome::Draw;
                }
            }
        }
        return Outcome::Ongoing;
    }

    [[nodiscard]] Outcome terminal_outcome() const {
        const Outcome decided = outcome_before_mobility();
        if (decided != Outcome::Ongoing) return decided;
        return get_legal_moves().empty() ? Outcome::Draw : Outcome::Ongoing;
    }

    [[nodiscard]] std::uint64_t position_hash() const noexcept {
        std::uint64_t hash = 0xCBF29CE484222325ULL;
        const auto mix = [&hash](std::uint64_t value) {
            hash ^= value;
            hash *= 0x100000001B3ULL;
        };

        for (Player cell : board) mix(static_cast<std::uint8_t>(cell));
        mix(blue_bin.size());
        mix(red_bin.size());
        mix(static_cast<std::uint8_t>(next_player));
        mix(static_cast<std::uint8_t>(rules.edge));
        mix(static_cast<std::uint8_t>(rules.all_on_board));
        mix(static_cast<std::uint8_t>(rules.move_when));
        mix(static_cast<std::uint8_t>(rules.move_how));
        mix(rules.zero_move_allowed);
        mix(rules.jumps_allowed);
        return hash;
    }

private:
    struct Cursor {
        int row;
        int column;
        int delta_row;
        int delta_column;
    };

    [[nodiscard]] static constexpr bool in_bounds(int row, int column) noexcept {
        return row >= 0 && row < height && column >= 0 && column < width;
    }

    [[nodiscard]] bool advance(Cursor& cursor) const noexcept {
        int next_row = cursor.row + cursor.delta_row;
        int next_column = cursor.column + cursor.delta_column;
        if (in_bounds(next_row, next_column)) {
            cursor.row = next_row;
            cursor.column = next_column;
            return true;
        }

        if (rules.edge == EdgeRule::Torus) {
            cursor.row = (next_row + height) % height;
            cursor.column = (next_column + width) % width;
            return true;
        }

        if (rules.edge == EdgeRule::Klein) {
            if (next_column < 0) next_column = width - 1;
            if (next_column >= width) next_column = 0;
            if (next_row < 0 || next_row >= height) {
                next_row = next_row < 0 ? height - 1 : 0;
                next_column = width - 1 - next_column;
                cursor.delta_column = -cursor.delta_column;
            }
            cursor.row = next_row;
            cursor.column = next_column;
            return true;
        }

        return false;
    }

    void append_moves_from(std::uint8_t from, std::vector<Move>& moves) const {
        if (rules.zero_move_allowed) {
            moves.push_back({MoveKind::MoveOnBoard, from, from});
        }

        if (rules.move_how == MoveHowRule::Anywhere) {
            for (std::uint8_t to = 0; to < board_size; ++to) {
                if (board[to] == Player::None) {
                    moves.push_back({MoveKind::MoveOnBoard, from, to});
                }
            }
            return;
        }

        static constexpr std::array<std::array<int, 2>, 4> rook_directions{{
            {{-1, 0}}, {{1, 0}}, {{0, -1}}, {{0, 1}},
        }};
        static constexpr std::array<std::array<int, 2>, 4> bishop_directions{{
            {{-1, -1}}, {{-1, 1}}, {{1, -1}}, {{1, 1}},
        }};

        const auto append_direction = [&](int delta_row, int delta_column, bool single_step) {
            int row = row_of(from) + delta_row;
            int column = column_of(from) + delta_column;
            while (in_bounds(row, column)) {
                const std::uint8_t to = square(row, column);
                if (board[to] == Player::None) {
                    moves.push_back({MoveKind::MoveOnBoard, from, to});
                } else if (!rules.jumps_allowed) {
                    break;
                }
                if (single_step) break;
                row += delta_row;
                column += delta_column;
            }
        };

        const bool king = rules.move_how == MoveHowRule::King;
        if (king || rules.move_how == MoveHowRule::Rook || rules.move_how == MoveHowRule::Queen) {
            for (const auto& direction : rook_directions) {
                append_direction(direction[0], direction[1], king);
            }
        }
        if (king || rules.move_how == MoveHowRule::Bishop || rules.move_how == MoveHowRule::Queen) {
            for (const auto& direction : bishop_directions) {
                append_direction(direction[0], direction[1], king);
            }
        }
    }

    [[nodiscard]] std::pair<bool, bool> line_winners() const noexcept {
        static constexpr std::array<std::array<int, 2>, 4> directions{{
            {{0, 1}}, {{1, 0}}, {{1, 1}}, {{1, -1}},
        }};

        bool blue = false;
        bool red = false;
        for (std::uint8_t start = 0; start < board_size; ++start) {
            const Player player = board[start];
            if (player == Player::None) continue;

            for (const auto& direction : directions) {
                Cursor cursor{row_of(start), column_of(start), direction[0], direction[1]};
                bool line = true;
                for (int length = 1; length < 3; ++length) {
                    if (!advance(cursor) || board[square(cursor.row, cursor.column)] != player) {
                        line = false;
                        break;
                    }
                }
                if (line) {
                    blue |= player == Player::Blue;
                    red |= player == Player::Red;
                }
            }
        }
        return {blue, red};
    }
};

class FastRng {
public:
    explicit FastRng(std::uint64_t seed) noexcept : state_(seed) {}

    [[nodiscard]] std::uint64_t next() noexcept {
        std::uint64_t value = (state_ += 0x9E3779B97F4A7C15ULL);
        value = (value ^ (value >> 30U)) * 0xBF58476D1CE4E5B9ULL;
        value = (value ^ (value >> 27U)) * 0x94D049BB133111EBULL;
        return value ^ (value >> 31U);
    }

    [[nodiscard]] std::size_t index(std::size_t size) noexcept {
        assert(size != 0);
        return static_cast<std::size_t>(next() % size);
    }

private:
    std::uint64_t state_;
};

struct MCTSNode {
    static constexpr std::uint32_t no_parent = std::numeric_limits<std::uint32_t>::max();

    GameState state;
    std::uint32_t parent{no_parent};
    Move move_from_parent{};
    Player player_just_moved{Player::None};
    std::vector<std::uint32_t> children;
    std::vector<Move> untried_moves;
    std::uint32_t visits{0};
    double value_sum{0.0};

    MCTSNode(GameState node_state, std::uint32_t parent_index,
             Move move, Player mover)
        : state(std::move(node_state)),
          parent(parent_index),
          move_from_parent(move),
          player_just_moved(mover) {
        if (state.terminal_outcome() == Outcome::Ongoing) {
            untried_moves = state.get_legal_moves();
        }
        children.reserve(untried_moves.size());
    }

    [[nodiscard]] double mean_value() const noexcept {
        return visits == 0 ? 0.0 : value_sum / static_cast<double>(visits);
    }
};

struct MCTSConfig {
    std::uint32_t iterations{100'000};
    std::uint32_t rollout_ply_limit{512};
    double exploration{1.4142135623730951};
    std::uint64_t seed{0xC001D00D5EEDULL};
};

struct SearchResult {
    Move move;
    std::uint32_t visits{0};
    double expected_score{0.0};
};

class MCTS {
public:
    explicit MCTS(MCTSConfig config = {}) : config_(config), rng_(config.seed) {
        if (config_.iterations == 0 || config_.rollout_ply_limit == 0) {
            throw std::invalid_argument("MCTS limits must be non-zero");
        }
        arena_.reserve(static_cast<std::size_t>(config_.iterations) + 1U);
    }

    [[nodiscard]] std::optional<SearchResult> search(const GameState& root_state) {
        arena_.clear();
        arena_.emplace_back(root_state, MCTSNode::no_parent, Move{},
                            opponent(root_state.next_player));
        if (arena_.front().state.terminal_outcome() != Outcome::Ongoing) {
            return std::nullopt;
        }

        for (std::uint32_t iteration = 0; iteration < config_.iterations; ++iteration) {
            std::uint32_t node_index = 0;
            while (arena_[node_index].untried_moves.empty() &&
                   !arena_[node_index].children.empty()) {
                node_index = select_child(node_index);
            }
            if (!arena_[node_index].untried_moves.empty()) {
                node_index = expand(node_index);
            }

            const Outcome outcome = rollout(arena_[node_index].state);
            backpropagate(node_index, outcome);
        }

        const MCTSNode& root = arena_.front();
        if (root.children.empty()) return std::nullopt;

        const auto best = std::max_element(
            root.children.begin(), root.children.end(),
            [this](std::uint32_t lhs, std::uint32_t rhs) {
                return arena_[lhs].visits < arena_[rhs].visits;
            });
        const MCTSNode& node = arena_[*best];
        return SearchResult{node.move_from_parent, node.visits, node.mean_value()};
    }

    [[nodiscard]] std::size_t nodes_allocated() const noexcept { return arena_.size(); }

private:
    [[nodiscard]] std::uint32_t select_child(std::uint32_t parent_index) const {
        const MCTSNode& parent = arena_[parent_index];
        const double log_parent = std::log(static_cast<double>(std::max(1U, parent.visits)));
        std::uint32_t best_index = parent.children.front();
        double best_score = -std::numeric_limits<double>::infinity();

        for (std::uint32_t child_index : parent.children) {
            const MCTSNode& child = arena_[child_index];
            const double score = child.visits == 0
                ? std::numeric_limits<double>::infinity()
                : child.mean_value() + config_.exploration *
                      std::sqrt(log_parent / static_cast<double>(child.visits));
            if (score > best_score) {
                best_score = score;
                best_index = child_index;
            }
        }
        return best_index;
    }

    [[nodiscard]] std::uint32_t expand(std::uint32_t parent_index) {
        const std::size_t move_index = rng_.index(arena_[parent_index].untried_moves.size());
        const Move move = arena_[parent_index].untried_moves[move_index];
        std::swap(arena_[parent_index].untried_moves[move_index],
                  arena_[parent_index].untried_moves.back());
        arena_[parent_index].untried_moves.pop_back();

        GameState child_state = arena_[parent_index].state;
        const Player mover = child_state.next_player;
        child_state.apply_move(move);

        const auto child_index = static_cast<std::uint32_t>(arena_.size());
        arena_.emplace_back(std::move(child_state), parent_index, move, mover);
        arena_[parent_index].children.push_back(child_index);
        return child_index;
    }

    [[nodiscard]] Outcome rollout(GameState state) {
        std::unordered_set<std::uint64_t> visited;
        visited.reserve(config_.rollout_ply_limit);

        for (std::uint32_t depth = 0; depth < config_.rollout_ply_limit; ++depth) {
            const Outcome decided = state.outcome_before_mobility();
            if (decided != Outcome::Ongoing) return decided;

            if (!visited.insert(state.position_hash()).second) {
                return Outcome::Draw;
            }

            std::vector<Move> moves = state.get_legal_moves();
            if (moves.empty()) return Outcome::Draw;
            state.apply_move(moves[rng_.index(moves.size())]);
        }
        return Outcome::Draw;
    }

    [[nodiscard]] static double reward(Player player, Outcome outcome) noexcept {
        if (outcome == Outcome::Draw) return 0.5;
        if (outcome == Outcome::BlueWin) return player == Player::Blue ? 1.0 : 0.0;
        if (outcome == Outcome::RedWin) return player == Player::Red ? 1.0 : 0.0;
        return 0.5;
    }

    void backpropagate(std::uint32_t node_index, Outcome outcome) {
        while (node_index != MCTSNode::no_parent) {
            MCTSNode& node = arena_[node_index];
            ++node.visits;
            node.value_sum += reward(node.player_just_moved, outcome);
            node_index = node.parent;
        }
    }

    MCTSConfig config_;
    FastRng rng_;
    std::vector<MCTSNode> arena_;
};

} // namespace pop_tac_toe

#endif // POP_TAC_TOE_MCTS_INCLUDED

#ifdef POP_TAC_TOE_STANDALONE
namespace {

template <typename Integer>
bool parse_integer(const char* text, Integer& value) {
    const std::string_view input(text);
    const auto result = std::from_chars(input.data(), input.data() + input.size(), value);
    return result.ec == std::errc{} && result.ptr == input.data() + input.size();
}

void print_move(const pop_tac_toe::Move& move) {
    using pop_tac_toe::GameState;
    if (move.kind == pop_tac_toe::MoveKind::PlaceFromBin) {
        std::cout << "move=place";
    } else {
        std::cout << "move=travel"
                  << " from_row=" << GameState::row_of(move.from)
                  << " from_column=" << GameState::column_of(move.from);
    }
    std::cout << " to_row=" << GameState::row_of(move.to)
              << " to_column=" << GameState::column_of(move.to) << '\n';
}

} // namespace

int main(int argc, char** argv) {
    using namespace pop_tac_toe;

    std::uint32_t iterations = 100'000;
    std::uint8_t checker_count = 8;
    std::string_view preset = "torus";

    std::uint32_t parsed_checkers = checker_count;
    if ((argc > 1 && (!parse_integer(argv[1], iterations) || iterations == 0)) ||
        (argc > 2 && (!parse_integer(argv[2], parsed_checkers) ||
                      parsed_checkers < 3 || parsed_checkers > 16)) ||
        (argc > 3 && (preset = argv[3], preset != "torus" && preset != "beginner")) ||
        argc > 4) {
        std::cerr << "Usage: " << argv[0]
                  << " [iterations] [checkers-per-player:3-16] [torus|beginner]\n";
        return 2;
    }
    checker_count = static_cast<std::uint8_t>(parsed_checkers);

    RuleConfig rules = preset == "beginner"
        ? RuleConfig::beginner()
        : RuleConfig::computer_torus();
    rules.blue_checkers = checker_count;
    rules.red_checkers = checker_count;

    GameState state(rules);
    MCTSConfig search_config;
    search_config.iterations = iterations;
    MCTS search(search_config);

    const auto start = std::chrono::steady_clock::now();
    const std::optional<SearchResult> result = search.search(state);
    const double seconds = std::chrono::duration<double>(
        std::chrono::steady_clock::now() - start).count();

    if (!result) {
        std::cout << "The supplied position is terminal or has no legal move.\n";
        return 1;
    }

    std::cout << "preset=" << preset
              << " checkers_per_player=" << static_cast<unsigned>(checker_count)
              << " iterations=" << iterations << '\n';
    print_move(result->move);
    std::cout << "visits=" << result->visits
              << " expected_score=" << result->expected_score << '\n'
              << "seconds=" << seconds
              << " iterations_per_second="
              << static_cast<double>(iterations) / seconds << '\n';
    return 0;
}
#endif
