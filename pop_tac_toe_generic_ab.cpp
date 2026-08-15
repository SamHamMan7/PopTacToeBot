#ifndef POP_TAC_TOE_GENERIC_AB_INCLUDED
#define POP_TAC_TOE_GENERIC_AB_INCLUDED

#include <algorithm>
#include <array>
#include <bit>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <optional>
#include <stdexcept>
#include <vector>

#include "pop_tac_toe_mcts.cpp"

namespace pop_tac_toe::generic_ab {

constexpr int mate_score = 1'000'000;
constexpr int infinity = 2'000'000;
constexpr std::uint16_t no_move = 0xFFFF;

struct Config {
    std::uint32_t time_limit_ms{1'000};
    std::uint8_t max_depth{64};
    std::size_t transposition_megabytes{64};
    std::uint64_t node_limit{0};
};

struct Stats {
    std::uint64_t nodes{0};
    std::uint64_t tt_hits{0};
    std::uint64_t tt_cutoffs{0};
    std::uint64_t beta_cutoffs{0};
};

struct Result {
    Move move{};
    int score{0};
    std::uint8_t completed_depth{0};
    double seconds{0.0};
    Stats stats{};
    std::vector<Move> principal_variation;
};

struct Key {
    std::uint64_t blue{0};
    std::uint64_t red{0};
    std::uint8_t blue_bin{0};
    std::uint8_t red_bin{0};
    Player next{Player::Blue};

    [[nodiscard]] friend constexpr bool operator==(const Key&, const Key&) = default;
};

[[nodiscard]] Key key_of(const GameState& state) noexcept {
    Key key;
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

[[nodiscard]] std::uint64_t mix64(std::uint64_t value) noexcept {
    value += 0x9E3779B97F4A7C15ULL;
    value = (value ^ (value >> 30U)) * 0xBF58476D1CE4E5B9ULL;
    value = (value ^ (value >> 27U)) * 0x94D049BB133111EBULL;
    return value ^ (value >> 31U);
}

[[nodiscard]] std::uint64_t hash_key(const Key& key) noexcept {
    std::uint64_t hash = mix64(key.blue);
    hash ^= std::rotl(mix64(key.red), 21);
    const std::uint64_t metadata = static_cast<std::uint64_t>(key.blue_bin) |
        (static_cast<std::uint64_t>(key.red_bin) << 8U) |
        (static_cast<std::uint64_t>(key.next) << 16U);
    return hash ^ std::rotl(mix64(metadata), 43);
}

[[nodiscard]] constexpr std::uint16_t encode_move(Move move) noexcept {
    const std::uint16_t from = move.kind == MoveKind::PlaceFromBin
        ? 64U
        : static_cast<std::uint16_t>(move.from);
    return static_cast<std::uint16_t>((from << 6U) | move.to);
}

[[nodiscard]] constexpr Move decode_move(std::uint16_t encoded) noexcept {
    const std::uint8_t from = static_cast<std::uint8_t>((encoded >> 6U) & 0x7FU);
    const std::uint8_t to = static_cast<std::uint8_t>(encoded & 0x3FU);
    if (from == 64U) return {MoveKind::PlaceFromBin, Move::no_square, to};
    return {MoveKind::MoveOnBoard, from, to};
}

enum class Bound : std::uint8_t { Empty = 0, Exact, Lower, Upper };

struct TTEntry {
    Key key{};
    std::int32_t score{0};
    std::uint16_t best_move{no_move};
    std::uint16_t generation{0};
    std::uint8_t depth{0};
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

    [[nodiscard]] const TTEntry* find(const Key& key) const noexcept {
        const TTEntry& entry = entries_[hash_key(key) & mask_];
        return entry.bound != Bound::Empty && entry.key == key ? &entry : nullptr;
    }

    void store(const Key& key,
               std::uint8_t depth,
               int score,
               Bound bound,
               std::uint16_t best_move) noexcept {
        TTEntry& entry = entries_[hash_key(key) & mask_];
        const bool same = entry.bound != Bound::Empty && entry.key == key;
        if (!same && entry.bound != Bound::Empty &&
            entry.generation == generation_ && entry.depth > depth) {
            return;
        }
        if (same && entry.depth > depth && entry.bound == Bound::Exact &&
            bound != Bound::Exact) {
            return;
        }
        entry.key = key;
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
    std::vector<TTEntry> entries_;
    std::size_t mask_{0};
    std::uint16_t generation_{1};
};

[[nodiscard]] bool is_beginner_rules(const RuleConfig& rules) noexcept {
    return rules.edge == EdgeRule::Reincarnation &&
        rules.all_on_board == AllOnBoardRule::Continue &&
        rules.move_when == MoveWhenRule::AllOnBoard &&
        rules.move_how == MoveHowRule::King &&
        !rules.zero_move_allowed && !rules.jumps_allowed;
}

[[nodiscard]] constexpr bool in_bounds(int row, int column) noexcept {
    return row >= 0 && row < GameState::height &&
           column >= 0 && column < GameState::width;
}

[[nodiscard]] int line_potential(const GameState& state, Player player) noexcept {
    static constexpr std::array<std::array<int, 2>, 4> directions{{
        {{0, 1}}, {{1, 0}}, {{1, 1}}, {{1, -1}},
    }};
    const Player other = opponent(player);
    int score = 0;
    for (int row = 0; row < GameState::height; ++row) {
        for (int column = 0; column < GameState::width; ++column) {
            for (const auto& direction : directions) {
                const int end_row = row + 2 * direction[0];
                const int end_column = column + 2 * direction[1];
                if (!in_bounds(end_row, end_column)) continue;
                int ours = 0;
                int theirs = 0;
                for (int step = 0; step < 3; ++step) {
                    const Player cell = state.board[GameState::square(
                        row + step * direction[0],
                        column + step * direction[1])];
                    ours += cell == player ? 1 : 0;
                    theirs += cell == other ? 1 : 0;
                }
                const int empty = 3 - ours - theirs;
                if (theirs == 0) {
                    if (ours == 2 && empty == 1) score += 90;
                    else if (ours == 1 && empty == 2) score += 8;
                }
                if (ours == 0) {
                    if (theirs == 2 && empty == 1) score -= 100;
                    else if (theirs == 1 && empty == 2) score -= 8;
                }
            }
        }
    }
    return score;
}

[[nodiscard]] int adjacent_pairs(const GameState& state, Player player) noexcept {
    static constexpr std::array<std::array<int, 2>, 4> directions{{
        {{0, 1}}, {{1, 0}}, {{1, 1}}, {{1, -1}},
    }};
    int pairs = 0;
    for (int row = 0; row < GameState::height; ++row) {
        for (int column = 0; column < GameState::width; ++column) {
            if (state.board[GameState::square(row, column)] != player) continue;
            for (const auto& direction : directions) {
                const int other_row = row + direction[0];
                const int other_column = column + direction[1];
                if (in_bounds(other_row, other_column) &&
                    state.board[GameState::square(other_row, other_column)] == player) {
                    ++pairs;
                }
            }
        }
    }
    return pairs;
}

class AlphaBetaBot {
public:
    explicit AlphaBetaBot(Config config = {})
        : config_(config), table_(config.transposition_megabytes) {
        if (config_.time_limit_ms == 0 || config_.max_depth == 0) {
            throw std::invalid_argument("alpha-beta limits must be non-zero");
        }
    }

    [[nodiscard]] std::optional<Result> search(const GameState& root) {
        if (!is_beginner_rules(root.rules)) {
            throw std::invalid_argument(
                "Generic AlphaBetaBot currently supports Beginner/Reincarnation + Continue + Move When All On Board + King");
        }
        if (root.terminal_outcome() != Outcome::Ongoing) return std::nullopt;

        const std::vector<Move> legal = root.get_legal_moves();
        if (legal.empty()) return std::nullopt;

        const auto start = std::chrono::steady_clock::now();
        deadline_ = start + std::chrono::milliseconds(config_.time_limit_ms);
        stats_ = {};
        stopped_ = false;
        table_.new_generation();
        path_[0] = key_of(root);

        for (const Move move : legal) {
            GameState child = root;
            child.apply_move(move);
            const Outcome outcome = child.terminal_outcome();
            if (is_win_for(outcome, root.next_player)) {
                Result result;
                result.move = move;
                result.score = mate_score;
                result.completed_depth = 1;
                result.seconds = std::chrono::duration<double>(
                    std::chrono::steady_clock::now() - start).count();
                result.stats = stats_;
                result.principal_variation.push_back(move);
                return result;
            }
        }

        Move best_move = legal.front();
        int best_score = 0;
        std::uint8_t completed_depth = 0;
        Move preferred = best_move;

        for (std::uint8_t depth = 1; depth <= config_.max_depth; ++depth) {
            const RootIteration iteration = search_root(root, legal, depth, preferred);
            if (!iteration.complete) break;
            best_move = iteration.move;
            best_score = iteration.score;
            preferred = iteration.move;
            completed_depth = depth;
            if (std::abs(best_score) == mate_score) break;
        }

        Result result;
        result.move = best_move;
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
    struct SearchValue {
        int score{0};
        bool complete{true};
    };

    struct Candidate {
        Move move{};
        GameState child;
        int order{0};
    };

    struct RootIteration {
        Move move{};
        int score{0};
        bool complete{true};
    };

    [[nodiscard]] static bool is_win_for(Outcome outcome, Player player) noexcept {
        return (player == Player::Blue && outcome == Outcome::BlueWin) ||
               (player == Player::Red && outcome == Outcome::RedWin);
    }

    [[nodiscard]] bool should_stop() noexcept {
        if (stopped_) return true;
        if (config_.node_limit != 0 && stats_.nodes >= config_.node_limit) {
            stopped_ = true;
            return true;
        }
        if ((stats_.nodes & 255ULL) == 0 &&
            std::chrono::steady_clock::now() >= deadline_) {
            stopped_ = true;
        }
        return stopped_;
    }

    [[nodiscard]] int terminal_score(const GameState& state) const {
        const Outcome outcome = state.terminal_outcome();
        if (outcome == Outcome::Ongoing) return infinity;
        if (outcome == Outcome::Draw) return 0;
        return is_win_for(outcome, state.next_player) ? mate_score : -mate_score;
    }

    [[nodiscard]] int evaluate(const GameState& state) const noexcept {
        const Player us = state.next_player;
        const Player them = opponent(us);
        int score = line_potential(state, us);
        score += 14 * (adjacent_pairs(state, us) - adjacent_pairs(state, them));
        score += 3 * (static_cast<int>(state.on_board(us)) -
                      static_cast<int>(state.on_board(them)));
        score -= 2 * (static_cast<int>(state.bin(us).size()) -
                      static_cast<int>(state.bin(them).size()));
        return score;
    }

    [[nodiscard]] int move_order(const GameState& parent,
                                 Move move,
                                 const GameState& child,
                                 std::uint16_t tt_move,
                                 Move preferred) const {
        int order = 0;
        const std::uint16_t encoded = encode_move(move);
        if (encoded == tt_move) order += 1'000'000'000;
        if (move == preferred) order += 900'000'000;
        const Outcome outcome = child.terminal_outcome();
        if (is_win_for(outcome, parent.next_player)) return order + 800'000'000;
        if (outcome == Outcome::Draw) order += 10'000'000;
        order += -evaluate(child);
        return order;
    }

    [[nodiscard]] RootIteration search_root(const GameState& root,
                                            const std::vector<Move>& legal,
                                            std::uint8_t depth,
                                            Move preferred) {
        std::vector<Candidate> candidates;
        candidates.reserve(legal.size());
        const Key root_key = key_of(root);
        const TTEntry* entry = table_.find(root_key);
        const std::uint16_t tt_move = entry == nullptr ? no_move : entry->best_move;
        for (const Move move : legal) {
            GameState child = root;
            child.apply_move(move);
            candidates.push_back({move, std::move(child), 0});
            candidates.back().order = move_order(
                root, move, candidates.back().child, tt_move, preferred);
        }
        std::stable_sort(candidates.begin(), candidates.end(),
                         [](const Candidate& left, const Candidate& right) {
                             return left.order > right.order;
                         });

        int alpha = -infinity;
        int best = -infinity;
        Move best_move = candidates.front().move;
        for (const Candidate& candidate : candidates) {
            const SearchValue child = negamax(
                candidate.child,
                static_cast<std::uint8_t>(depth - 1),
                -infinity,
                -alpha,
                1);
            if (!child.complete) return {best_move, best, false};
            const int score = -child.score;
            if (score > best) {
                best = score;
                best_move = candidate.move;
            }
            alpha = std::max(alpha, score);
        }
        table_.store(root_key, depth, best, Bound::Exact, encode_move(best_move));
        return {best_move, best, true};
    }

    [[nodiscard]] SearchValue negamax(const GameState& state,
                                      std::uint8_t depth,
                                      int alpha,
                                      int beta,
                                      std::uint8_t ply) {
        ++stats_.nodes;
        if (should_stop()) return {0, false};

        const int terminal = terminal_score(state);
        if (terminal != infinity) return {terminal, true};
        if (depth == 0) return {evaluate(state), true};

        const Key key = key_of(state);
        for (std::uint8_t index = 0; index < ply; ++index) {
            if (path_[index] == key) return {0, true};
        }
        if (ply >= path_.size()) return {evaluate(state), true};
        path_[ply] = key;

        const int original_alpha = alpha;
        const TTEntry* entry = table_.find(key);
        std::uint16_t tt_move = no_move;
        if (entry != nullptr) {
            ++stats_.tt_hits;
            tt_move = entry->best_move;
            if (entry->depth >= depth) {
                if (entry->bound == Bound::Exact) return {entry->score, true};
                if (entry->bound == Bound::Lower) alpha = std::max(alpha, static_cast<int>(entry->score));
                if (entry->bound == Bound::Upper) beta = std::min(beta, static_cast<int>(entry->score));
                if (alpha >= beta) {
                    ++stats_.tt_cutoffs;
                    return {entry->score, true};
                }
            }
        }

        const std::vector<Move> legal = state.get_legal_moves();
        if (legal.empty()) return {0, true};

        std::vector<Candidate> candidates;
        candidates.reserve(legal.size());
        for (const Move move : legal) {
            GameState child = state;
            child.apply_move(move);
            int order = move_order(state, move, child, tt_move, Move{});
            candidates.push_back({move, std::move(child), order});
        }
        std::stable_sort(candidates.begin(), candidates.end(),
                         [](const Candidate& left, const Candidate& right) {
                             return left.order > right.order;
                         });

        int best = -infinity;
        Move best_move = candidates.front().move;
        bool cutoff = false;
        for (const Candidate& candidate : candidates) {
            const SearchValue child = negamax(
                candidate.child,
                static_cast<std::uint8_t>(depth - 1),
                -beta,
                -alpha,
                static_cast<std::uint8_t>(ply + 1));
            if (!child.complete) return {0, false};
            const int score = -child.score;
            if (score > best) {
                best = score;
                best_move = candidate.move;
            }
            alpha = std::max(alpha, score);
            if (alpha >= beta) {
                cutoff = true;
                ++stats_.beta_cutoffs;
                break;
            }
        }

        Bound bound = Bound::Exact;
        if (best <= original_alpha) bound = Bound::Upper;
        else if (cutoff || best >= beta) bound = Bound::Lower;
        table_.store(key, depth, best, bound, encode_move(best_move));
        return {best, true};
    }

    [[nodiscard]] std::vector<Move> extract_pv(GameState state,
                                               std::uint8_t depth,
                                               Move root_move) const {
        std::vector<Move> pv;
        pv.reserve(depth);
        Move move = root_move;
        for (std::uint8_t ply = 0; ply < depth; ++ply) {
            const std::vector<Move> legal = state.get_legal_moves();
            if (std::find(legal.begin(), legal.end(), move) == legal.end()) break;
            pv.push_back(move);
            state.apply_move(move);
            if (state.terminal_outcome() != Outcome::Ongoing) break;
            const TTEntry* entry = table_.find(key_of(state));
            if (entry == nullptr || entry->best_move == no_move) break;
            move = decode_move(entry->best_move);
        }
        return pv;
    }

    Config config_;
    TranspositionTable table_;
    Stats stats_{};
    bool stopped_{false};
    std::chrono::steady_clock::time_point deadline_{};
    std::array<Key, 128> path_{};
};

} // namespace pop_tac_toe::generic_ab

#endif // POP_TAC_TOE_GENERIC_AB_INCLUDED
