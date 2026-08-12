#include <algorithm>
#include <cstdint>
#include <exception>
#include <functional>
#include <initializer_list>
#include <iostream>
#include <stdexcept>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "pop_tac_toe_mcts.cpp"
#include "pop_tac_toe_strong.cpp"

namespace {

using namespace pop_tac_toe;

struct PieceAt {
    Player player;
    int row;
    int column;
};

[[noreturn]] void fail(std::string_view message) {
    throw std::runtime_error(std::string(message));
}

void require(bool condition, std::string_view message) {
    if (!condition) fail(message);
}

GameState make_state(
    RuleConfig rules,
    std::initializer_list<PieceAt> pieces = {},
    Player next_player = Player::Blue,
    std::uint32_t ply = 1) {
    GameState state(rules);
    std::fill(state.board.begin(), state.board.end(), Player::None);

    std::size_t blue_count = 0;
    std::size_t red_count = 0;
    for (const PieceAt& piece : pieces) {
        require(piece.row >= 0 && piece.row < GameState::height,
                "test piece row is outside the board");
        require(piece.column >= 0 && piece.column < GameState::width,
                "test piece column is outside the board");
        const std::uint8_t square = GameState::square(piece.row, piece.column);
        require(state.board[square] == Player::None,
                "test setup places two pieces on one square");
        require(piece.player != Player::None,
                "test setup cannot place an empty piece");
        state.board[square] = piece.player;
        blue_count += piece.player == Player::Blue;
        red_count += piece.player == Player::Red;
    }

    require(blue_count <= rules.blue_checkers,
            "test setup has too many blue pieces");
    require(red_count <= rules.red_checkers,
            "test setup has too many red pieces");
    state.blue_bin.assign(rules.blue_checkers - blue_count, 1);
    state.red_bin.assign(rules.red_checkers - red_count, 1);
    state.next_player = next_player;
    state.ply = ply;
    return state;
}

Player cell(const GameState& state, int row, int column) {
    return state.board[GameState::square(row, column)];
}

RuleConfig rules_for(EdgeRule edge, std::uint8_t checkers = 8) {
    RuleConfig rules = RuleConfig::beginner();
    rules.edge = edge;
    rules.blue_checkers = checkers;
    rules.red_checkers = checkers;
    return rules;
}

void test_adjacent_piece_moves_one_square_away() {
    GameState state = make_state(
        rules_for(EdgeRule::Reincarnation),
        {{Player::Red, 3, 4}});

    state.apply_pop_mechanic(GameState::square(3, 3));

    require(cell(state, 3, 4) == Player::None,
            "the adjacent square should be vacated");
    require(cell(state, 3, 5) == Player::Red,
            "the adjacent checker should move exactly one square away");
}

void test_checker_directly_behind_blocks_push() {
    GameState state = make_state(
        rules_for(EdgeRule::Reincarnation),
        {{Player::Blue, 3, 4}, {Player::Red, 3, 5}});

    state.apply_pop_mechanic(GameState::square(3, 3));

    require(cell(state, 3, 4) == Player::Blue,
            "a checker with another checker directly behind it must not move");
    require(cell(state, 3, 5) == Player::Red,
            "the blocking checker must remain in place");
}

void test_all_eight_pushes_are_simultaneous() {
    GameState state = make_state(
        rules_for(EdgeRule::Reincarnation),
        {
            {Player::Blue, 2, 2}, {Player::Red, 2, 3},
            {Player::Blue, 2, 4}, {Player::Red, 3, 2},
            {Player::Blue, 3, 4}, {Player::Red, 4, 2},
            {Player::Blue, 4, 3}, {Player::Red, 4, 4},
        });

    state.apply_pop_mechanic(GameState::square(3, 3));

    const std::initializer_list<PieceAt> expected{
        {Player::Blue, 1, 1}, {Player::Red, 1, 3},
        {Player::Blue, 1, 5}, {Player::Red, 3, 1},
        {Player::Blue, 3, 5}, {Player::Red, 5, 1},
        {Player::Blue, 5, 3}, {Player::Red, 5, 5},
    };
    for (const PieceAt& piece : expected) {
        require(cell(state, piece.row, piece.column) == piece.player,
                "one of the eight simultaneous pushes reached the wrong square");
    }

    for (int row = 2; row <= 4; ++row) {
        for (int column = 2; column <= 4; ++column) {
            if (row == 3 && column == 3) continue;
            require(cell(state, row, column) == Player::None,
                    "an adjacent source square should be empty after its push");
        }
    }
}

void test_reincarnation_returns_piece_to_owners_bin() {
    GameState state = make_state(
        rules_for(EdgeRule::Reincarnation, 3),
        {{Player::Red, 0, 0}});
    const std::size_t before = state.red_bin.size();

    state.apply_pop_mechanic(GameState::square(0, 1));

    require(cell(state, 0, 0) == Player::None,
            "a reincarnated edge checker should leave its square");
    require(state.red_bin.size() == before + 1,
            "a reincarnated checker must return to its owner's bin");
    require(state.blue_bin.size() == 3,
            "reincarnation must not change the other player's bin");
}

void test_torus_wraps_across_edge() {
    GameState state = make_state(
        rules_for(EdgeRule::Torus, 3),
        {{Player::Red, 0, 0}});

    state.apply_pop_mechanic(GameState::square(0, 1));

    require(cell(state, 0, 0) == Player::None,
            "the torus source square should be vacated");
    require(cell(state, 0, 7) == Player::Red,
            "a checker pushed left off the torus must wrap to column seven");
}

void test_klein_vertical_wrap_reverses_column() {
    GameState state = make_state(
        rules_for(EdgeRule::Klein, 3),
        {{Player::Blue, 0, 1}});

    state.apply_pop_mechanic(GameState::square(1, 1));

    require(cell(state, 0, 1) == Player::None,
            "the Klein source square should be vacated");
    require(cell(state, 7, 6) == Player::Blue,
            "vertical Klein wrapping must reverse the column");
}

void test_win_is_checked_after_pop() {
    RuleConfig rules = rules_for(EdgeRule::Reincarnation, 4);
    GameState state = make_state(
        rules,
        {
            {Player::Blue, 3, 4},
            {Player::Blue, 3, 6},
            {Player::Blue, 3, 7},
        },
        Player::Blue);

    state.apply_move({MoveKind::PlaceFromBin, Move::no_square,
                      GameState::square(3, 3)});

    require(cell(state, 3, 4) == Player::None,
            "the adjacent checker should move before the win check");
    require(cell(state, 3, 5) == Player::Blue,
            "the push should complete the post-pop line");
    require(state.terminal_outcome() == Outcome::BlueWin,
            "the post-pop three-in-a-row should win for blue");
}

void test_pre_pop_line_does_not_count() {
    RuleConfig rules = rules_for(EdgeRule::Reincarnation, 3);
    GameState state = make_state(
        rules,
        {{Player::Blue, 3, 2}, {Player::Blue, 3, 4}},
        Player::Blue);

    state.apply_move({MoveKind::PlaceFromBin, Move::no_square,
                      GameState::square(3, 3)});

    require(cell(state, 3, 1) == Player::Blue,
            "the left checker should be pushed left");
    require(cell(state, 3, 5) == Player::Blue,
            "the right checker should be pushed right");
    require(state.terminal_outcome() == Outcome::Ongoing,
            "a line that existed only before popping must not win");
}

void test_simultaneous_lines_are_a_draw() {
    RuleConfig rules = rules_for(EdgeRule::Reincarnation, 3);
    GameState state = make_state(
        rules,
        {
            {Player::Blue, 0, 0}, {Player::Blue, 0, 1},
            {Player::Blue, 0, 2}, {Player::Red, 7, 5},
            {Player::Red, 7, 6}, {Player::Red, 7, 7},
        });

    require(state.terminal_outcome() == Outcome::Draw,
            "simultaneous blue and red lines must be a draw");
}

void test_torus_winning_line_wraps() {
    RuleConfig rules = rules_for(EdgeRule::Torus, 3);
    GameState state = make_state(
        rules,
        {
            {Player::Blue, 2, 7},
            {Player::Blue, 2, 0},
            {Player::Blue, 2, 1},
        });

    require(state.terminal_outcome() == Outcome::BlueWin,
            "a torus line crossing columns 7, 0, and 1 must count as a win");
}

void test_bin_piece_must_be_placed_before_travel() {
    RuleConfig rules = rules_for(EdgeRule::Reincarnation, 3);
    GameState state = make_state(
        rules,
        {{Player::Blue, 2, 2}},
        Player::Blue);

    const std::vector<Move> with_bin = state.get_legal_moves();
    require(!with_bin.empty(), "the player should have legal placements");
    require(std::all_of(with_bin.begin(), with_bin.end(), [](const Move& move) {
                return move.kind == MoveKind::PlaceFromBin;
            }),
            "travel must be unavailable while the player's bin is nonempty");

    state = make_state(
        rules,
        {
            {Player::Blue, 0, 0},
            {Player::Blue, 3, 3},
            {Player::Blue, 7, 7},
        },
        Player::Blue);
    const std::vector<Move> empty_bin = state.get_legal_moves();
    require(!empty_bin.empty(), "travel should be available once the bin is empty");
    require(std::all_of(empty_bin.begin(), empty_bin.end(), [](const Move& move) {
                return move.kind == MoveKind::MoveOnBoard;
            }),
            "only travel moves should remain once the bin is empty");
}

void test_travel_triggers_pop() {
    RuleConfig rules = rules_for(EdgeRule::Reincarnation, 3);
    GameState state = make_state(
        rules,
        {
            {Player::Blue, 0, 0},
            {Player::Blue, 3, 3},
            {Player::Blue, 7, 7},
            {Player::Red, 3, 5},
        },
        Player::Blue);

    state.apply_move({MoveKind::MoveOnBoard,
                      GameState::square(3, 3),
                      GameState::square(3, 4)});

    require(cell(state, 3, 3) == Player::None,
            "travel must vacate its source square");
    require(cell(state, 3, 4) == Player::Blue,
            "the traveling checker must occupy its destination");
    require(cell(state, 3, 5) == Player::None &&
                cell(state, 3, 6) == Player::Red,
            "placing the traveling checker must trigger the pop mechanic");
}

void test_position_identity_supports_repetition_draws() {
    RuleConfig rules = rules_for(EdgeRule::Torus, 3);
    GameState first = make_state(
        rules,
        {{Player::Blue, 1, 1}, {Player::Red, 4, 4}},
        Player::Blue,
        10);
    GameState same = first;
    same.ply = 500;

    require(first.position_hash() == same.position_hash(),
            "move number must not distinguish an otherwise repeated position");

    same.next_player = Player::Red;
    require(first.position_hash() != same.position_hash(),
            "side to move must distinguish repetition positions");
}

strong::FastMove to_fast_move(Move move) {
    return {
        move.kind == MoveKind::PlaceFromBin ? strong::no_square : move.from,
        move.to,
    };
}

void test_strong_bitboard_matches_reference_rules() {
    FastRng random(0xD1FF3E3ULL);
    RuleConfig rules = RuleConfig::computer_torus();
    rules.blue_checkers = 3;
    rules.red_checkers = 3;
    std::uint64_t checked_transitions = 0;

    for (int game = 0; game < 100; ++game) {
        GameState state(rules);
        for (int ply = 0; ply < 64; ++ply) {
            const strong::Position compact = strong::make_position(state);
            require(strong::terminal_outcome(compact) == state.terminal_outcome(),
                    "strong position disagrees about the terminal outcome");
            const std::vector<Move> legal = state.get_legal_moves();
            const strong::MoveList fast_legal = strong::generate_moves(compact);
            require(legal.size() == fast_legal.size,
                    "strong position generated a different legal move count");
            if (state.terminal_outcome() != Outcome::Ongoing) break;

            const Move move = legal[random.index(legal.size())];
            GameState reference_child = state;
            reference_child.apply_move(move);
            const strong::Position compact_child =
                strong::apply_move(compact, to_fast_move(move));
            require(strong::make_position(reference_child) == compact_child,
                    "strong bitboard transition differs from GameState");
            state = std::move(reference_child);
            ++checked_transitions;
        }
    }
    require(checked_transitions > 1'000,
            "strong differential test covered too few transitions");
}

bool can_force_win(GameState state, Player target, int remaining_plies) {
    const Outcome outcome = state.terminal_outcome();
    if (outcome != Outcome::Ongoing) {
        return (target == Player::Blue && outcome == Outcome::BlueWin) ||
               (target == Player::Red && outcome == Outcome::RedWin);
    }
    if (remaining_plies == 0) return false;

    const bool target_turn = state.next_player == target;
    for (const Move move : state.get_legal_moves()) {
        GameState child = state;
        child.apply_move(move);
        const bool child_value =
            can_force_win(std::move(child), target, remaining_plies - 1);
        if (target_turn && child_value) return true;
        if (!target_turn && !child_value) return false;
    }
    return !target_turn;
}

void test_strong_bot_avoids_recorded_tactical_fork() {
    GameState state(RuleConfig::computer_torus());
    const auto place = [](int row, int column) {
        return Move{
            MoveKind::PlaceFromBin,
            Move::no_square,
            GameState::square(row, column),
        };
    };
    const std::array<Move, 6> history{{
        place(3, 1), place(4, 1), place(1, 1),
        place(5, 1), place(4, 2), place(2, 1),
    }};
    for (const Move move : history) state.apply_move(move);

    strong::AlphaBetaConfig config;
    config.time_limit_ms = 10'000;
    config.max_depth = 4;
    config.transposition_megabytes = 4;
    strong::AlphaBetaBot bot(config);
    const std::optional<strong::AlphaBetaResult> result = bot.search(state);
    require(result.has_value(), "strong bot returned no tactical move");
    require(result->completed_depth == 4,
            "strong bot did not complete the tactical search depth");

    state.apply_move(result->move);
    require(!can_force_win(state, Player::Red, 3),
            "strong bot repeated the recorded mate-in-two blunder");
}

class TestRunner {
public:
    void run(std::string_view name, const std::function<void()>& test) {
        try {
            test();
            ++passed_;
            std::cout << "PASS  " << name << '\n';
        } catch (const std::exception& error) {
            ++failed_;
            std::cerr << "FAIL  " << name << ": " << error.what() << '\n';
        } catch (...) {
            ++failed_;
            std::cerr << "FAIL  " << name << ": unknown exception\n";
        }
    }

    int finish() const {
        std::cout << "\n" << passed_ << " passed, " << failed_ << " failed\n";
        return failed_ == 0 ? 0 : 1;
    }

private:
    int passed_{0};
    int failed_{0};
};

} // namespace

int main() {
    TestRunner runner;
    runner.run("adjacent piece moves one square away",
               test_adjacent_piece_moves_one_square_away);
    runner.run("checker directly behind blocks push",
               test_checker_directly_behind_blocks_push);
    runner.run("all eight pushes are simultaneous",
               test_all_eight_pushes_are_simultaneous);
    runner.run("reincarnation returns piece to owner's bin",
               test_reincarnation_returns_piece_to_owners_bin);
    runner.run("torus wraps across edge", test_torus_wraps_across_edge);
    runner.run("Klein vertical wrap reverses column",
               test_klein_vertical_wrap_reverses_column);
    runner.run("win is checked after pop", test_win_is_checked_after_pop);
    runner.run("pre-pop line does not count", test_pre_pop_line_does_not_count);
    runner.run("simultaneous lines are a draw",
               test_simultaneous_lines_are_a_draw);
    runner.run("torus winning line wraps", test_torus_winning_line_wraps);
    runner.run("bin piece must be placed before travel",
               test_bin_piece_must_be_placed_before_travel);
    runner.run("travel triggers pop", test_travel_triggers_pop);
    runner.run("position identity supports repetition draws",
               test_position_identity_supports_repetition_draws);
    runner.run("strong bitboard matches reference rules",
               test_strong_bitboard_matches_reference_rules);
    runner.run("strong bot avoids recorded tactical fork",
               test_strong_bot_avoids_recorded_tactical_fork);
    return runner.finish();
}
