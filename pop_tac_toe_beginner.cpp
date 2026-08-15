#include <algorithm>
#include <charconv>
#include <chrono>
#include <cstdint>
#include <iomanip>
#include <iostream>
#include <optional>
#include <random>
#include <sstream>
#include <string>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "pop_tac_toe_generic_ab.cpp"

namespace ptt_beginner {
using namespace pop_tac_toe;

constexpr std::uint32_t max_plies = 512;

struct Key {
    std::uint64_t blue{0}, red{0};
    std::uint8_t blue_bin{0}, red_bin{0};
    Player next{Player::Blue};
    friend bool operator==(const Key&, const Key&) = default;
};
struct KeyHash {
    std::size_t operator()(const Key& k) const noexcept {
        auto mix=[](std::uint64_t x){x^=x>>33;x*=0xff51afd7ed558ccdULL;x^=x>>33;x*=0xc4ceb9fe1a85ec53ULL;x^=x>>33;return x;};
        return static_cast<std::size_t>(mix(k.blue)^std::rotl(mix(k.red),21)^
          (static_cast<std::uint64_t>(k.blue_bin)<<8)^k.red_bin^
          (static_cast<std::uint64_t>(k.next)<<20));
    }
};
Key key_of(const GameState& s){
    Key k;
    for(std::uint8_t i=0;i<64;++i){if(s.board[i]==Player::Blue)k.blue|=1ULL<<i;else if(s.board[i]==Player::Red)k.red|=1ULL<<i;}
    k.blue_bin=static_cast<std::uint8_t>(s.blue_bin.size());k.red_bin=static_cast<std::uint8_t>(s.red_bin.size());k.next=s.next_player;return k;
}

template<class T> bool parse_num(std::string_view text,T& out){auto [p,e]=std::from_chars(text.data(),text.data()+text.size(),out);return e==std::errc{}&&p==text.data()+text.size();}
const char* name(Player p){return p==Player::Blue?"Blue":p==Player::Red?"Red":"None";}
char mark(Player p){return p==Player::Blue?'B':p==Player::Red?'R':'.';}
std::string move_text(Move m){auto sq=[](std::uint8_t s){return "("+std::to_string(GameState::row_of(s))+","+std::to_string(GameState::column_of(s))+")";};return m.kind==MoveKind::PlaceFromBin?"P"+sq(m.to):"T"+sq(m.from)+"->"+sq(m.to);}
bool legal(const GameState& s,Move m){auto v=s.get_legal_moves();return std::find(v.begin(),v.end(),m)!=v.end();}
void board(const GameState& s){
    std::cout<<"\n    0 1 2 3 4 5 6 7\n   +-----------------+\n";
    for(int r=0;r<8;++r){std::cout<<' '<<r<<" | ";for(int c=0;c<8;++c){std::cout<<mark(s.board[GameState::square(r,c)])<<(c==7?'\n':' ');} }
    std::cout<<"   +-----------------+\nBlue bin="<<s.blue_bin.size()<<"  Red bin="<<s.red_bin.size()<<"  Turn="<<name(s.next_player)<<"  Ply="<<s.ply<<"\n";
}
void result(Outcome o){if(o==Outcome::BlueWin)std::cout<<"Blue wins.\n";else if(o==Outcome::RedWin)std::cout<<"Red wins.\n";else std::cout<<"Draw.\n";}

std::optional<Move> parse_move(const std::string& line){
    std::istringstream in(line);std::string cmd;in>>cmd;
    if(cmd=="p"||cmd=="place"){int r,c;if(!(in>>r>>c)||r<0||r>7||c<0||c>7)return std::nullopt;return Move{MoveKind::PlaceFromBin,Move::no_square,GameState::square(r,c)};}
    if(cmd=="t"||cmd=="travel"){int r1,c1,r2,c2;if(!(in>>r1>>c1>>r2>>c2)||r1<0||r1>7||c1<0||c1>7||r2<0||r2>7||c2<0||c2>7)return std::nullopt;return Move{MoveKind::MoveOnBoard,GameState::square(r1,c1),GameState::square(r2,c2)};}
    return std::nullopt;
}

int play(int argc,char** argv){
    Player human=Player::Blue;std::uint32_t ms=3000,checkers=8;
    if(argc>2){std::string_view c=argv[2];if(c=="blue")human=Player::Blue;else if(c=="red")human=Player::Red;else return 2;}
    if(argc>3){std::string_view b=argv[3];if(!b.starts_with("ab:" )||!parse_num(b.substr(3),ms)||ms==0)return 2;}
    if(argc>4&&(!parse_num(std::string_view(argv[4]),checkers)||checkers<3||checkers>16))return 2;
    RuleConfig rules=RuleConfig::beginner();rules.blue_checkers=static_cast<std::uint8_t>(checkers);rules.red_checkers=static_cast<std::uint8_t>(checkers);GameState s(rules);
    generic_ab::Config cfg;cfg.time_limit_ms=ms;cfg.transposition_megabytes=64;generic_ab::AlphaBetaBot bot(cfg);
    std::unordered_set<Key,KeyHash> seen;seen.insert(key_of(s));
    std::cout<<"Pop Tac Toe Beginner terminal\nRules: Reincarnation + Continue + Move When All On Board + King\nYou are "<<name(human)<<". Commands: p ROW COL, t R1 C1 R2 C2, moves, quit\n";
    for(;;){
        board(s);auto out=s.terminal_outcome();if(out!=Outcome::Ongoing){result(out);return 0;}if(s.ply>=max_plies){std::cout<<"Draw by ply limit.\n";return 0;}
        Move m;
        if(s.next_player==human){
            for(;;){std::cout<<"you> "<<std::flush;std::string line;if(!std::getline(std::cin,line))return 0;if(line=="quit"||line=="q")return 0;if(line=="moves"){for(auto x:s.get_legal_moves())std::cout<<move_text(x)<<' ';std::cout<<'\n';continue;}auto pm=parse_move(line);if(pm&&legal(s,*pm)){m=*pm;break;}std::cout<<"Illegal/invalid move.\n";}
        }else{
            std::cout<<"Computer thinking..."<<std::flush;auto r=bot.search(s);if(!r){std::cerr<<" no move\n";return 1;}m=r->move;std::cout<<" done: "<<move_text(m)<<" score="<<r->score<<" depth="<<unsigned(r->completed_depth)<<" nodes="<<r->stats.nodes<<" time="<<std::fixed<<std::setprecision(3)<<r->seconds<<"s\n";
        }
        s.apply_move(m);if(!seen.insert(key_of(s)).second){board(s);std::cout<<"Draw by repetition.\n";return 0;}
    }
}

int watch(int argc,char** argv){
    std::uint32_t games=1,ms=1000,opening=6,checkers=8;std::uint64_t seed=123456;
    if(argc>2&&!parse_num(std::string_view(argv[2]),games))return 2;
    if(argc>3&&!parse_num(std::string_view(argv[3]),ms))return 2;
    if(argc>4&&!parse_num(std::string_view(argv[4]),opening))return 2;
    if(argc>5&&!parse_num(std::string_view(argv[5]),seed))return 2;
    if(argc>6&&!parse_num(std::string_view(argv[6]),checkers))return 2;
    if(games==0||ms==0||opening>32||checkers<3||checkers>16)return 2;
    std::uint32_t bw=0,rw=0,dr=0;
    for(std::uint32_t g=0;g<games;++g){RuleConfig rules=RuleConfig::beginner();rules.blue_checkers=checkers;rules.red_checkers=checkers;GameState s(rules);generic_ab::Config cfg;cfg.time_limit_ms=ms;cfg.transposition_megabytes=128;generic_ab::AlphaBetaBot bot(cfg);std::mt19937_64 rng(seed+g);std::unordered_set<Key,KeyHash> seen;seen.insert(key_of(s));Outcome out=Outcome::Ongoing;
        std::cout<<"Game "<<(g+1)<<" seed="<<(seed+g)<<" beginner checkers="<<checkers<<"\n";
        while(out==Outcome::Ongoing&&s.ply<max_plies){Move m;if(s.ply<opening){auto mv=s.get_legal_moves();m=mv[static_cast<std::size_t>(rng()%mv.size())];std::cout<<name(s.next_player)<<" "<<move_text(m)<<" opening\n";}else{auto r=bot.search(s);if(!r)break;m=r->move;std::cout<<name(s.next_player)<<" "<<move_text(m)<<" depth="<<unsigned(r->completed_depth)<<" nodes="<<r->stats.nodes<<"\n";}s.apply_move(m);if(!seen.insert(key_of(s)).second){out=Outcome::Draw;break;}out=s.terminal_outcome();}
        if(out==Outcome::BlueWin)++bw;else if(out==Outcome::RedWin)++rw;else ++dr;result(out);
    }
    std::cout<<"Summary blue="<<bw<<" red="<<rw<<" draws="<<dr<<"\n";return 0;
}

int selftest(){RuleConfig r=RuleConfig::beginner();GameState s(r);generic_ab::Config c;c.time_limit_ms=10;c.transposition_megabytes=1;generic_ab::AlphaBetaBot b(c);auto x=b.search(s);if(!x||!legal(s,x->move)){std::cerr<<"SELF_TEST_FAIL\n";return 1;}std::cout<<"SELF_TEST_PASS beginner_alpha_beta=yes move="<<move_text(x->move)<<"\n";return 0;}
void usage(const char* p){std::cerr<<"Usage:\n  "<<p<<" selftest\n  "<<p<<" play [blue|red] [ab:MILLISECONDS] [checkers:3-16]\n  "<<p<<" watch [games] [think-ms] [opening-plies] [seed] [checkers:3-16]\nExamples:\n  "<<p<<" play blue ab:3000 8\n  "<<p<<" watch 20 1000 8 123456 8\n";}
}

int main(int argc,char** argv){using namespace ptt_beginner;if(argc<2){usage(argv[0]);return 2;}std::string_view mode=argv[1];if(mode=="selftest")return selftest();if(mode=="play")return play(argc,argv);if(mode=="watch")return watch(argc,argv);usage(argv[0]);return 2;}
