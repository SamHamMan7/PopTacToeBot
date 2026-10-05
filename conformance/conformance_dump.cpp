#include <algorithm>
#include <cstdint>
#include <initializer_list>
#include <iostream>
#include <string_view>

#include "../pop_tac_toe_mcts.cpp"

namespace {

using namespace pop_tac_toe;

struct PieceAt {
    Player player;
    int row;
    int column;
};

RuleConfig rules_for(EdgeRule edge, std::uint8_t checkers = 8) {
    RuleConfig rules = RuleConfig::beginner();
    rules.edge = edge;
    rules.blue_checkers = checkers;
    rules.red_checkers = checkers;
    return rules;
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
        const auto sq = GameState::square(piece.row, piece.column);
        state.board[sq] = piece.player;
        blue_count += piece.player == Player::Blue;
        red_count += piece.player == Player::Red;
    }

    state.blue_bin.assign(rules.blue_checkers - blue_count, 1);
    state.red_bin.assign(rules.red_checkers - red_count, 1);
    state.next_player = next_player;
    state.ply = ply;
    return state;
}

char piece_char(Player player) {
    switch (player) {
    case Player::Blue: return 'B';
    case Player::Red: return 'R';
    default: return '.';
    }
}

std::string_view outcome_name(Outcome outcome) {
    switch (outcome) {
    case Outcome::BlueWin: return "blueWin";
    case Outcome::RedWin: return "redWin";
    case Outcome::Draw: return "draw";
    default: return "ongoing";
    }
}

void emit(std::string_view id, const GameState& state) {
    std::cout << id << '|';
    for (Player cell : state.board) std::cout << piece_char(cell);
    std::cout << '|' << state.blue_bin.size()
              << '|' << state.red_bin.size()
              << '|' << (state.next_player == Player::Blue ? "blue" : "red")
              << '|' << state.ply
              << '|' << outcome_name(state.terminal_outcome())
              << '\n';
}

} // namespace

int main() {
    {
        GameState s = make_state(rules_for(EdgeRule::Reincarnation),
                                 {{Player::Red, 3, 4}});
        s.apply_pop_mechanic(GameState::square(3, 3));
        emit("adjacent", s);
    }
    {
        GameState s = make_state(rules_for(EdgeRule::Reincarnation),
                                 {{Player::Blue, 3, 4}, {Player::Red, 3, 5}});
        s.apply_pop_mechanic(GameState::square(3, 3));
        emit("blocked", s);
    }
    {
        GameState s = make_state(
            rules_for(EdgeRule::Reincarnation),
            {
                {Player::Blue, 2, 2}, {Player::Red, 2, 3},
                {Player::Blue, 2, 4}, {Player::Red, 3, 2},
                {Player::Blue, 3, 4}, {Player::Red, 4, 2},
                {Player::Blue, 4, 3}, {Player::Red, 4, 4},
            });
        s.apply_pop_mechanic(GameState::square(3, 3));
        emit("eight", s);
    }
    {
        GameState s = make_state(rules_for(EdgeRule::Reincarnation, 3),
                                 {{Player::Red, 0, 0}});
        s.apply_pop_mechanic(GameState::square(0, 1));
        emit("reincarnate", s);
    }
    {
        GameState s = make_state(rules_for(EdgeRule::Torus, 3),
                                 {{Player::Red, 0, 0}});
        s.apply_pop_mechanic(GameState::square(0, 1));
        emit("torus", s);
    }
    {
        GameState s = make_state(rules_for(EdgeRule::Klein, 3),
                                 {{Player::Blue, 0, 1}});
        s.apply_pop_mechanic(GameState::square(1, 1));
        emit("klein", s);
    }
    {
        GameState s = make_state(
            rules_for(EdgeRule::Reincarnation, 4),
            {
                {Player::Blue, 3, 4},
                {Player::Blue, 3, 6},
                {Player::Blue, 3, 7},
            },
            Player::Blue);
        s.apply_move({MoveKind::PlaceFromBin, Move::no_square,
                      GameState::square(3, 3)});
        emit("postpopwin", s);
    }
    {
        GameState s = make_state(
            rules_for(EdgeRule::Reincarnation, 3),
            {{Player::Blue, 3, 2}, {Player::Blue, 3, 4}},
            Player::Blue);
        s.apply_move({MoveKind::PlaceFromBin, Move::no_square,
                      GameState::square(3, 3)});
        emit("prepop", s);
    }
    {
        GameState s = make_state(
            rules_for(EdgeRule::Reincarnation, 3),
            {
                {Player::Blue, 0, 0}, {Player::Blue, 0, 1},
                {Player::Blue, 0, 2}, {Player::Red, 7, 5},
                {Player::Red, 7, 6}, {Player::Red, 7, 7},
            });
        emit("simdraw", s);
    }
    {
        GameState s = make_state(
            rules_for(EdgeRule::Torus, 3),
            {
                {Player::Blue, 2, 7},
                {Player::Blue, 2, 0},
                {Player::Blue, 2, 1},
            });
        emit("torusline", s);
    }
    {
        GameState s = make_state(
            rules_for(EdgeRule::Reincarnation, 3),
            {
                {Player::Blue, 0, 0},
                {Player::Blue, 3, 3},
                {Player::Blue, 7, 7},
                {Player::Red, 3, 5},
            },
            Player::Blue);
        s.apply_move({MoveKind::MoveOnBoard,
                      GameState::square(3, 3),
                      GameState::square(3, 4)});
        emit("travelpop", s);
    }
}
