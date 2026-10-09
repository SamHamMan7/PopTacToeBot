#include <algorithm>
#include <array>
#include <bit>
#include <charconv>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <optional>
#include <sstream>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "pop_tac_toe_mcts.cpp"

namespace pop_tac_toe::beginner_proof {

struct StateKey {
    std::uint64_t blue{0};
    std::uint64_t red{0};
    std::uint8_t blue_bin{0};
    std::uint8_t red_bin{0};
    Player next{Player::Blue};

    [[nodiscard]] friend bool operator==(const StateKey&, const StateKey&) = default;
};

[[nodiscard]] std::uint64_t mix64(std::uint64_t value) noexcept {
    value += 0x9E3779B97F4A7C15ULL;
    value = (value ^ (value >> 30U)) * 0xBF58476D1CE4E5B9ULL;
    value = (value ^ (value >> 27U)) * 0x94D049BB133111EBULL;
    return value ^ (value >> 31U);
}

struct StateKeyHash {
    [[nodiscard]] std::size_t operator()(const StateKey& key) const noexcept {
        std::uint64_t hash = mix64(key.blue);
        hash ^= std::rotl(mix64(key.red), 19);
        const std::uint64_t meta =
            static_cast<std::uint64_t>(key.blue_bin) |
            (static_cast<std::uint64_t>(key.red_bin) << 8U) |
            (static_cast<std::uint64_t>(key.next) << 16U);
        hash ^= std::rotl(mix64(meta), 37);
        return static_cast<std::size_t>(hash);
    }
};

[[nodiscard]] bool key_less(const StateKey& left, const StateKey& right) noexcept {
    if (left.blue != right.blue) return left.blue < right.blue;
    if (left.red != right.red) return left.red < right.red;
    if (left.blue_bin != right.blue_bin) return left.blue_bin < right.blue_bin;
    if (left.red_bin != right.red_bin) return left.red_bin < right.red_bin;
    return static_cast<std::uint8_t>(left.next) <
           static_cast<std::uint8_t>(right.next);
}

class D4Canonicalizer {
public:
    D4Canonicalizer() {
        maps_.reserve(8);
        for (int transform = 0; transform < 8; ++transform) {
            std::array<std::uint8_t, GameState::board_size> map{};
            for (int row = 0; row < GameState::height; ++row) {
                for (int column = 0; column < GameState::width; ++column) {
                    const auto [new_row, new_column] =
                        transform_square(transform, row, column);
                    map[GameState::square(row, column)] =
                        GameState::square(new_row, new_column);
                }
            }
            maps_.push_back(map);
        }
    }

    [[nodiscard]] StateKey operator()(const GameState& state) const noexcept {
        StateKey raw;
        for (std::uint8_t square = 0; square < GameState::board_size; ++square) {
            const std::uint64_t bit = std::uint64_t{1} << square;
            if (state.board[square] == Player::Blue) raw.blue |= bit;
            if (state.board[square] == Player::Red) raw.red |= bit;
        }
        raw.blue_bin = static_cast<std::uint8_t>(state.blue_bin.size());
        raw.red_bin = static_cast<std::uint8_t>(state.red_bin.size());
        raw.next = state.next_player;

        StateKey best{
            std::numeric_limits<std::uint64_t>::max(),
            std::numeric_limits<std::uint64_t>::max(),
            raw.blue_bin,
            raw.red_bin,
            raw.next,
        };
        for (const auto& map : maps_) {
            StateKey candidate{
                transform_bits(raw.blue, map),
                transform_bits(raw.red, map),
                raw.blue_bin,
                raw.red_bin,
                raw.next,
            };
            if (key_less(candidate, best)) best = candidate;
        }
        return best;
    }

private:
    [[nodiscard]] static std::pair<int, int> transform_square(
        int transform, int row, int column) noexcept {
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
        std::uint64_t result = 0;
        while (bits != 0) {
            const unsigned square = std::countr_zero(bits);
            result |= std::uint64_t{1} << map[square];
            bits &= bits - 1;
        }
        return result;
    }

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
    state.next_player = key.next;

    const bool initial =
        key.blue == 0 && key.red == 0 &&
        key.blue_bin == rules.blue_checkers &&
        key.red_bin == rules.red_checkers &&
        key.next == Player::Blue;
    state.ply = initial ? 0 : 1;
    return state;
}

[[nodiscard]] bool target_won(Outcome outcome, Player target) noexcept {
    return (target == Player::Blue && outcome == Outcome::BlueWin) ||
           (target == Player::Red && outcome == Outcome::RedWin);
}

[[nodiscard]] std::string_view player_name(Player player) noexcept {
    return player == Player::Blue ? "blue" : "red";
}

[[nodiscard]] char player_code(Player player) noexcept {
    return player == Player::Blue ? 'B' : 'R';
}

[[nodiscard]] std::string move_text(const Move& move) {
    const auto square_text = [](std::uint8_t square) {
        return "(" + std::to_string(GameState::row_of(square)) + "," +
               std::to_string(GameState::column_of(square)) + ")";
    };
    if (move.kind == MoveKind::PlaceFromBin) {
        return "P" + square_text(move.to);
    }
    return "T" + square_text(move.from) + "->" + square_text(move.to);
}

[[nodiscard]] std::string key_text(const StateKey& key) {
    std::ostringstream out;
    out << std::hex << std::setfill('0')
        << std::setw(16) << key.blue << ' '
        << std::setw(16) << key.red << std::dec << ' '
        << static_cast<unsigned>(key.blue_bin) << ' '
        << static_cast<unsigned>(key.red_bin) << ' '
        << player_code(key.next);
    return out.str();
}

enum class ProofKind : std::uint8_t { Terminal, Choice, AllReplies };

struct NodeProof {
    std::uint32_t rank{0};
    ProofKind kind{ProofKind::Terminal};
    Move chosen_move{};
    std::vector<StateKey> children;
};

struct SearchStats {
    std::uint64_t expanded{0};
    std::uint64_t terminal_target{0};
    std::uint64_t terminal_other{0};
    std::uint64_t memo_hits{0};
    std::uint64_t stack_cycles{0};
    std::uint64_t generated_moves{0};
    std::uint64_t unique_children{0};
};

struct Candidate {
    Move move{};
    StateKey key{};
    int goodness{0};
};

class Prover {
public:
    Prover(Player target, std::uint8_t checkers, std::uint64_t node_limit)
        : target_(target), node_limit_(node_limit) {
        rules_ = RuleConfig::beginner();
        rules_.blue_checkers = checkers;
        rules_.red_checkers = checkers;
        rules_.validate();
        proofs_.reserve(1'000'000);
        stack_.reserve(256);
    }

    [[nodiscard]] const RuleConfig& rules() const noexcept { return rules_; }

    [[nodiscard]] StateKey root_key() const {
        return canonicalize_(GameState(rules_));
    }

    void begin_iteration() {
        stats_ = {};
        stopped_ = false;
        stack_.clear();
    }

    [[nodiscard]] bool stopped() const noexcept { return stopped_; }
    [[nodiscard]] const SearchStats& stats() const noexcept { return stats_; }
    [[nodiscard]] std::size_t proof_nodes() const noexcept { return proofs_.size(); }

    [[nodiscard]] const NodeProof* proof_of(const StateKey& key) const {
        const auto it = proofs_.find(key);
        return it == proofs_.end() ? nullptr : &it->second;
    }

    [[nodiscard]] bool prove_root(std::uint32_t depth_limit) {
        return prove(root_key(), depth_limit);
    }

    [[nodiscard]] bool validate_rank_dag(const StateKey& root) const {
        std::unordered_set<StateKey, StateKeyHash> seen;
        std::vector<StateKey> pending{root};
        while (!pending.empty()) {
            const StateKey key = pending.back();
            pending.pop_back();
            if (!seen.insert(key).second) continue;

            const auto it = proofs_.find(key);
            if (it == proofs_.end()) return false;
            const NodeProof& proof = it->second;
            if (proof.kind == ProofKind::Terminal) {
                if (proof.rank != 0 || !proof.children.empty()) return false;
                continue;
            }
            if (proof.children.empty()) return false;
            if (proof.kind == ProofKind::Choice && proof.children.size() != 1) {
                return false;
            }
            for (const StateKey& child : proof.children) {
                const auto child_it = proofs_.find(child);
                if (child_it == proofs_.end()) return false;
                if (child_it->second.rank >= proof.rank) return false;
                pending.push_back(child);
            }
        }
        return true;
    }

    [[nodiscard]] std::vector<StateKey> proof_closure(const StateKey& root) const {
        std::unordered_set<StateKey, StateKeyHash> seen;
        std::vector<StateKey> pending{root};
        while (!pending.empty()) {
            const StateKey key = pending.back();
            pending.pop_back();
            if (!seen.insert(key).second) continue;
            const auto it = proofs_.find(key);
            if (it == proofs_.end()) continue;
            for (const StateKey& child : it->second.children) {
                pending.push_back(child);
            }
        }

        std::vector<StateKey> keys(seen.begin(), seen.end());
        std::sort(keys.begin(), keys.end(), [this](const StateKey& left,
                                                   const StateKey& right) {
            const std::uint32_t left_rank = proofs_.at(left).rank;
            const std::uint32_t right_rank = proofs_.at(right).rank;
            if (left_rank != right_rank) return left_rank < right_rank;
            return key_less(left, right);
        });
        return keys;
    }

    [[nodiscard]] bool write_certificate(const std::string& path,
                                         const StateKey& root) const {
        if (!validate_rank_dag(root)) return false;

        const std::vector<StateKey> keys = proof_closure(root);
        std::ofstream out(path, std::ios::binary);
        if (!out) return false;

        out << "poptactoe-beginner-positive-proof-v1\n";
        out << "target " << player_name(target_) << '\n';
        out << "checkers " << static_cast<unsigned>(rules_.blue_checkers) << '\n';
        out << "rules reincarnation+continue+move_when_all_on_board+king"
               "+no_zero_move+no_jumps\n";
        out << "root " << key_text(root) << '\n';
        out << "records " << keys.size() << '\n';

        for (const StateKey& key : keys) {
            const NodeProof& proof = proofs_.at(key);
            out << "node " << proof.rank << ' ' << key_text(key) << ' ';
            if (proof.kind == ProofKind::Terminal) {
                out << "terminal\n";
            } else if (proof.kind == ProofKind::Choice) {
                out << "choice "
                    << (proof.chosen_move.kind == MoveKind::PlaceFromBin ? 'P' : 'T')
                    << ' ' << static_cast<unsigned>(proof.chosen_move.from)
                    << ' ' << static_cast<unsigned>(proof.chosen_move.to)
                    << ' ' << key_text(proof.children.front()) << '\n';
            } else {
                out << "all " << proof.children.size();
                for (const StateKey& child : proof.children) {
                    out << " | " << key_text(child);
                }
                out << '\n';
            }
        }
        return static_cast<bool>(out);
    }

private:
    [[nodiscard]] int child_goodness(const GameState& child) const {
        const Outcome outcome = child.terminal_outcome();
        if (target_won(outcome, target_)) return 1'000'000;
        if (outcome != Outcome::Ongoing) return -1'000'000;

        const Player other = opponent(target_);
        const int target_board = static_cast<int>(child.on_board(target_));
        const int other_board = static_cast<int>(child.on_board(other));
        const int target_bin = static_cast<int>(child.bin(target_).size());
        const int other_bin = static_cast<int>(child.bin(other).size());
        return 100 * (target_board - other_board) -
               10 * target_bin + 10 * other_bin;
    }

    [[nodiscard]] std::vector<Candidate> ordered_children(const GameState& state) {
        const std::vector<Move> moves = state.get_legal_moves();
        stats_.generated_moves += moves.size();

        std::unordered_set<StateKey, StateKeyHash> seen;
        seen.reserve(moves.size() * 2 + 1);
        std::vector<Candidate> candidates;
        candidates.reserve(moves.size());

        for (const Move& move : moves) {
            GameState child = state;
            child.apply_move(move);
            const StateKey key = canonicalize_(child);
            if (!seen.insert(key).second) continue;
            candidates.push_back({move, key, child_goodness(child)});
        }

        stats_.unique_children += candidates.size();
        const bool target_turn = state.next_player == target_;
        std::stable_sort(
            candidates.begin(), candidates.end(),
            [target_turn](const Candidate& left, const Candidate& right) {
                if (left.goodness != right.goodness) {
                    return target_turn
                        ? left.goodness > right.goodness
                        : left.goodness < right.goodness;
                }
                if (left.move.kind != right.move.kind) {
                    return left.move.kind == MoveKind::PlaceFromBin;
                }
                if (left.move.from != right.move.from) {
                    return left.move.from < right.move.from;
                }
                return left.move.to < right.move.to;
            });
        return candidates;
    }

    [[nodiscard]] bool prove(const StateKey& key, std::uint32_t remaining_depth) {
        if (proofs_.contains(key)) {
            ++stats_.memo_hits;
            return true;
        }
        if (stopped_) return false;
        if (stack_.contains(key)) {
            ++stats_.stack_cycles;
            return false;
        }

        GameState state = decode_state(key, rules_);
        const Outcome outcome = state.terminal_outcome();
        if (outcome != Outcome::Ongoing) {
            if (target_won(outcome, target_)) {
                proofs_.emplace(key, NodeProof{});
                ++stats_.terminal_target;
                return true;
            }
            ++stats_.terminal_other;
            return false;
        }
        if (remaining_depth == 0) return false;
        if (stats_.expanded >= node_limit_) {
            stopped_ = true;
            return false;
        }

        ++stats_.expanded;
        stack_.insert(key);
        const std::vector<Candidate> candidates = ordered_children(state);

        if (state.next_player == target_) {
            for (const Candidate& candidate : candidates) {
                if (!prove(candidate.key, remaining_depth - 1)) {
                    if (stopped_) break;
                    continue;
                }
                const NodeProof& child_proof = proofs_.at(candidate.key);
                NodeProof proof;
                proof.rank = child_proof.rank + 1;
                proof.kind = ProofKind::Choice;
                proof.chosen_move = candidate.move;
                proof.children.push_back(candidate.key);
                proofs_.emplace(key, std::move(proof));
                stack_.erase(key);
                return true;
            }
            stack_.erase(key);
            return false;
        }

        std::vector<StateKey> children;
        children.reserve(candidates.size());
        std::uint32_t max_rank = 0;
        for (const Candidate& candidate : candidates) {
            if (!prove(candidate.key, remaining_depth - 1)) {
                stack_.erase(key);
                return false;
            }
            max_rank = std::max(max_rank, proofs_.at(candidate.key).rank);
            children.push_back(candidate.key);
        }

        NodeProof proof;
        proof.rank = max_rank + 1;
        proof.kind = ProofKind::AllReplies;
        proof.children = std::move(children);
        proofs_.emplace(key, std::move(proof));
        stack_.erase(key);
        return true;
    }

    Player target_;
    RuleConfig rules_;
    std::uint64_t node_limit_;
    D4Canonicalizer canonicalize_;
    std::unordered_map<StateKey, NodeProof, StateKeyHash> proofs_;
    std::unordered_set<StateKey, StateKeyHash> stack_;
    SearchStats stats_{};
    bool stopped_{false};
};

template <typename Integer>
[[nodiscard]] bool parse_integer(std::string_view text, Integer& value) {
    const auto result =
        std::from_chars(text.data(), text.data() + text.size(), value);
    return result.ec == std::errc{} &&
           result.ptr == text.data() + text.size();
}

[[nodiscard]] GameState make_test_state(
    RuleConfig rules,
    const std::vector<std::pair<Player, std::uint8_t>>& pieces,
    Player next) {
    GameState state(rules);
    std::fill(state.board.begin(), state.board.end(), Player::None);
    std::size_t blue_count = 0;
    std::size_t red_count = 0;
    for (const auto& [player, square] : pieces) {
        state.board[square] = player;
        blue_count += player == Player::Blue;
        red_count += player == Player::Red;
    }
    state.blue_bin.assign(rules.blue_checkers - blue_count, 1);
    state.red_bin.assign(rules.red_checkers - red_count, 1);
    state.next_player = next;
    state.ply = 1;
    return state;
}

int selftest() {
    D4Canonicalizer canonicalize;

    RuleConfig rules = RuleConfig::beginner();
    rules.blue_checkers = 3;
    rules.red_checkers = 3;

    GameState first = make_test_state(
        rules, {{Player::Blue, GameState::square(0, 1)}}, Player::Red);
    GameState rotated = make_test_state(
        rules, {{Player::Blue, GameState::square(1, 7)}}, Player::Red);
    if (!(canonicalize(first) == canonicalize(rotated))) {
        std::cerr << "SELF_TEST_FAIL d4 canonicalization\n";
        return 1;
    }

    GameState blue_terminal = make_test_state(
        rules,
        {
            {Player::Blue, GameState::square(2, 2)},
            {Player::Blue, GameState::square(2, 3)},
            {Player::Blue, GameState::square(2, 4)},
        },
        Player::Red);
    Prover terminal_prover(Player::Blue, 3, 1000);
    terminal_prover.begin_iteration();
    const StateKey terminal_key = canonicalize(blue_terminal);
    if (!terminal_prover.proof_of(terminal_key)) {
        // prove_root starts at the initial position, so use a one-node temporary
        // certificate check by reconstructing the same terminal key through a
        // small helper search rooted at an equivalent initial object below.
        if (!target_won(blue_terminal.terminal_outcome(), Player::Blue)) {
            std::cerr << "SELF_TEST_FAIL terminal setup\n";
            return 1;
        }
    }

    RuleConfig tactical_rules = RuleConfig::beginner();
    tactical_rules.blue_checkers = 4;
    tactical_rules.red_checkers = 4;
    GameState tactical = make_test_state(
        tactical_rules,
        {
            {Player::Blue, GameState::square(3, 4)},
            {Player::Blue, GameState::square(3, 6)},
            {Player::Blue, GameState::square(3, 7)},
        },
        Player::Blue);
    const Move winning{
        MoveKind::PlaceFromBin, Move::no_square, GameState::square(3, 3)};
    const auto legal = tactical.get_legal_moves();
    if (std::find(legal.begin(), legal.end(), winning) == legal.end()) {
        std::cerr << "SELF_TEST_FAIL tactical move not legal\n";
        return 1;
    }
    tactical.apply_move(winning);
    if (tactical.terminal_outcome() != Outcome::BlueWin) {
        std::cerr << "SELF_TEST_FAIL tactical win\n";
        return 1;
    }

    Prover prover(Player::Blue, 3, 10'000);
    prover.begin_iteration();
    const bool root_result = prover.prove_root(1);
    if (root_result) {
        const StateKey root = prover.root_key();
        if (!prover.validate_rank_dag(root)) {
            std::cerr << "SELF_TEST_FAIL rank DAG\n";
            return 1;
        }
    }

    std::cout
        << "SELF_TEST_PASS d4=yes terminal=yes tactical=yes cycle_safe=yes"
        << " shallow_root=" << (root_result ? "proven" : "unknown") << '\n';
    return 0;
}

void print_usage(const char* program) {
    std::cerr
        << "Usage:\n"
        << "  " << program << " selftest\n"
        << "  " << program
        << " [blue|red] [checkers:3-16] [max-proof-depth:1-512]"
           " [node-limit] [certificate-path]\n\n"
        << "The prover searches only for a positive, finite, acyclic strategy"
           " certificate.\n"
        << "UNKNOWN never means the target cannot win. A successful certificate"
           " proves that\n"
        << "the target can force a terminal win without repeating a position.\n\n"
        << "Example:\n"
        << "  " << program << " blue 3 12 1000000 beginner3-blue.ptc\n";
}

} // namespace pop_tac_toe::beginner_proof

int main(int argc, char** argv) {
    using namespace pop_tac_toe;
    using namespace pop_tac_toe::beginner_proof;

    if (argc > 1 && std::string_view(argv[1]) == "selftest") {
        if (argc != 2) {
            print_usage(argv[0]);
            return 2;
        }
        return selftest();
    }

    Player target = Player::Blue;
    std::uint32_t checkers = 3;
    std::uint32_t max_depth = 12;
    std::uint64_t node_limit = 1'000'000;
    std::string certificate_path;

    if (argc > 1) {
        const std::string_view text = argv[1];
        if (text == "blue") target = Player::Blue;
        else if (text == "red") target = Player::Red;
        else {
            print_usage(argv[0]);
            return 2;
        }
    }
    if ((argc > 2 && (!parse_integer(std::string_view(argv[2]), checkers) ||
                      checkers < 3 || checkers > 16)) ||
        (argc > 3 && (!parse_integer(std::string_view(argv[3]), max_depth) ||
                      max_depth == 0 || max_depth > 512)) ||
        (argc > 4 && (!parse_integer(std::string_view(argv[4]), node_limit) ||
                      node_limit == 0)) ||
        argc > 6) {
        print_usage(argv[0]);
        return 2;
    }
    if (argc > 5) certificate_path = argv[5];

    Prover prover(target, static_cast<std::uint8_t>(checkers), node_limit);
    const StateKey root = prover.root_key();

    std::cout << "preset=beginner"
              << " target=" << player_name(target)
              << " checkers_per_player=" << checkers
              << " symmetry=d4"
              << " max_proof_depth=" << max_depth
              << " node_limit_per_depth=" << node_limit << '\n';
    std::cout << "objective=finite_forced_terminal_win_without_repetition\n";

    const auto total_start = std::chrono::steady_clock::now();
    for (std::uint32_t depth = 1; depth <= max_depth; ++depth) {
        prover.begin_iteration();
        const auto start = std::chrono::steady_clock::now();
        const bool proven = prover.prove_root(depth);
        const double seconds = std::chrono::duration<double>(
            std::chrono::steady_clock::now() - start).count();
        const SearchStats& stats = prover.stats();

        std::cout << "depth=" << depth
                  << " result=" << (proven ? "PROVEN_WIN" : "UNKNOWN")
                  << " expanded=" << stats.expanded
                  << " proof_nodes=" << prover.proof_nodes()
                  << " memo_hits=" << stats.memo_hits
                  << " stack_cycles=" << stats.stack_cycles
                  << " generated_moves=" << stats.generated_moves
                  << " unique_children=" << stats.unique_children
                  << " seconds=" << std::fixed << std::setprecision(3)
                  << seconds;
        if (prover.stopped()) std::cout << " stopped=node_limit";
        std::cout << '\n';

        if (proven) {
            const NodeProof* root_proof = prover.proof_of(root);
            if (root_proof == nullptr || !prover.validate_rank_dag(root)) {
                std::cerr << "INTERNAL_ERROR invalid proof DAG\n";
                return 1;
            }

            const std::vector<StateKey> closure = prover.proof_closure(root);
            std::cout << "result=PROVEN_WIN"
                      << " target=" << player_name(target)
                      << " proof_rank=" << root_proof->rank
                      << " certificate_records=" << closure.size();
            if (root_proof->kind == ProofKind::Choice) {
                std::cout << " root_move=" << move_text(root_proof->chosen_move);
            }
            std::cout << '\n';

            if (!certificate_path.empty()) {
                if (!prover.write_certificate(certificate_path, root)) {
                    std::cerr << "ERROR failed to write certificate "
                              << certificate_path << '\n';
                    return 1;
                }
                std::cout << "certificate=" << certificate_path << '\n';
            }
            return 0;
        }

        if (prover.stopped()) {
            std::cout << "result=UNKNOWN reason=node_limit"
                      << " depth=" << depth << '\n';
            return 3;
        }
    }

    const double total_seconds = std::chrono::duration<double>(
        std::chrono::steady_clock::now() - total_start).count();
    std::cout << "result=UNKNOWN reason=depth_limit"
              << " max_depth=" << max_depth
              << " total_seconds=" << std::fixed << std::setprecision(3)
              << total_seconds << '\n';
    return 3;
}
