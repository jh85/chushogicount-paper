// Straight reference port of full_pilot.verify and mode.mated(D13a/b).
// No planner geometry, hot-square shortcut, candidate pruning or search code.
#include <algorithm>
#include <iostream>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <unordered_set>
#include <vector>
#include "movegen.h"
#include "sfen.h"
#include "status.h"
#include "usi.h"

using chu::Position;
using chu::Color;
static const char* INITIAL =
 "lfcsgekgscfl/a1b1txot1b1a/mvrhdqndhrvm/pppppppppppp/3i4i3/12/12/"
 "3I4I3/PPPPPPPPPPPP/MVRHDNQDHRVM/A1B1TOXT1B1A/LFCSGKEGSCFL b - 1";

static uint8_t canonical_piece(uint8_t piece) {
 if (!piece) return 0;
 auto role=chu::roleOf(piece);
 if (role==chu::LionP) role=chu::Lion;
 if (role==chu::QueenP) role=chu::Queen;
 if (role==chu::Prince) role=chu::King;
 return chu::makePiece(role,chu::colorOf(piece));
}
static Position canonical(Position pos) {
 for (auto& piece:pos.board) piece=canonical_piece(piece);
 return pos;
}
static Position parse(const std::string& sfen) {
 Position p;
 p.rules=chu::RuleSet::JCSA;
 if (!chu::parseSfen(sfen,p)) throw std::invalid_argument("invalid SFEN");
 return p;
}
static bool royal(uint8_t p,Color side) {
 return p && chu::colorOf(p)==side && chu::isRoyal(chu::roleOf(p));
}
static int royal_count(const Position& p,Color side) {
 int count=0;
 for (auto piece:p.board) count+=royal(piece,side);
 return count;
}
static bool capturable(Position p,Color side,bool all=false) {
 p=canonical(p);
 p.sideToMove=!side;p.lastLionCapture=chu::kNoSquare;
 const int needed=all?royal_count(p,side):1;
 if (!needed) return false;
 for (const auto& move:chu::generateLegal(p)) {
  int taken=royal(p.board[move.to],side);
  if (move.mid!=chu::kNoSquare && move.mid!=move.to) taken+=royal(p.board[move.mid],side);
  if (taken>=needed) return true;
 }
 return false;
}
static bool mated(Position p) {
 p=canonical(p);
 const auto side=p.sideToMove;
 if (royal_count(p,side)!=1 || !capturable(p,side)) return false;
 const bool opponent_present=royal_count(p,!side)>0;
 for (const auto& move:chu::generateLegal(p)) {
  auto after=p;after.apply(move);
  // D13b: a capture of the last opposing royal(s) ends the game immediately.
  if (opponent_present && !royal_count(after,!side)) return false;
  // D13a: a new prince is an escape unless both royals can be taken at once.
  if (royal_count(after,side)>=2) {
   if (!capturable(after,side,true)) return false;
  } else if (!capturable(after,side)) return false;
 }
 return true;
}
static bool terminal(const Position& p) {
 return chu::evaluateStatus(p).end!=chu::GameEnd::Playing || mated(p);
}
using View=std::pair<bool,std::set<std::string>>;
static View view(Position p) {
 p=canonical(p);
 if (terminal(p)) return {true,{}};
 std::set<std::string> moves;
 for (const auto& move:chu::generateLegal(p)) moves.insert(chu::moveToUsi(move));
 return {false,moves};
}
static std::string key(const Position& p) {
 std::string out;
 for (auto piece:p.board) out.push_back(static_cast<char>(canonical_piece(piece)));
 out.push_back(static_cast<char>(p.sideToMove));
 out.push_back(static_cast<char>(p.lastLionCapture+1));
 return out;
}
static bool same_board(const Position& a,const Position& b) {
 for (int i=0;i<chu::kSquares;++i)
  if (canonical_piece(a.board[i])!=canonical_piece(b.board[i])) return false;
 return true;
}
static std::pair<bool,std::string> verify(const std::string& stratum,const Position& target,const std::vector<std::string>& moves) {
 if (stratum!="nonterm" && stratum!="flagsj" && stratum!="term") throw std::invalid_argument("invalid stratum");
 Position p=parse(INITIAL);
 std::unordered_set<std::string> seen;
 for (size_t i=0;i<moves.size();++i) {
  if (!seen.insert(key(p)).second) return {false,"repetition before ply "+std::to_string(i)};
  if (terminal(p)) return {false,"termination before ply "+std::to_string(i)};
  bool found=false;
  for (const auto& move:chu::generateLegal(p)) {
   // Exact protocol move strings, as in the independent Python legal set.
   if (chu::moveToUsi(move)==moves[i]) {p.apply(move);found=true;break;}
  }
  if (!found) return {false,"illegal at ply "+std::to_string(i)};
 }
 if (!same_board(p,target) || p.sideToMove!=chu::Sente) return {false,"wrong final board/turn"};
 if (stratum=="term") return {!royal_count(p,chu::Sente),"royals-lost target"};
 auto clear=canonical(p);clear.lastLionCapture=chu::kNoSquare;
 if (stratum=="nonterm") {
  if (p.lastLionCapture==chu::kNoSquare) return {true,"cleared final flag"};
  const auto actual=view(p);
  const bool same=actual==view(clear);
  return {same,same?(actual.first?"terminal flag collapsed into N":"ineffective continuing flag collapsed into N"):"cleared final flag required"};
 }
 if (p.lastLionCapture==chu::kNoSquare || target.lastLionCapture==chu::kNoSquare) return {false,"final flag absent"};
 auto wanted=canonical(p);wanted.lastLionCapture=target.lastLionCapture;
 const auto expected=view(wanted);
 if (expected==view(clear)) return {false,"no additional F state: terminal duplicate or ineffective flag"};
 const bool same=view(p)==expected;
 return {same,same && expected.first?"flag-induced terminal state":"effective flag equivalence"};
}
static std::vector<std::string> split(const std::string& line,char delimiter) {
 std::vector<std::string> parts;std::istringstream input(line);std::string part;
 while (std::getline(input,part,delimiter)) parts.push_back(part);
 return parts;
}
int main() {
 std::ios::sync_with_stdio(false);
 std::string line;
 while (std::getline(std::cin,line)) {
  try {
   const auto fields=split(line,'\t');
   if (fields.size()==2 && fields[0]=="mated") std::cout<<"ok\t"<<mated(parse(fields[1]))<<'\n';
   else if (fields.size()==2 && fields[0]=="view") {
    const auto value=view(parse(fields[1]));std::cout<<"ok\t"<<value.first<<'\t';
    for (const auto& move:value.second) std::cout<<move<<' ';
    std::cout<<'\n';
   } else if ((fields.size()==3 || fields.size()==4) && fields[0]=="verify") {
    // stratum and expected SFEN are themselves separated by one space-free tab.
    throw std::invalid_argument("verify requires stratum, SFEN and move field");
   } else if (fields.size()==5 && fields[0]=="verify") {
    std::istringstream list(fields[4]);std::vector<std::string> moves;std::string move;
    while (list>>move) moves.push_back(move);
    if (std::stoull(fields[3])!=moves.size()) throw std::invalid_argument("move count mismatch");
    const auto result=verify(fields[1],parse(fields[2]),moves);
    std::cout<<(result.first?"ok":"fail")<<'\t'<<result.second<<'\n';
   } else if (fields.size()==4 && fields[0]=="verify0") {
    if (fields[3]!="0") throw std::invalid_argument("zero move count required");
    const auto result=verify(fields[1],parse(fields[2]),{});
    std::cout<<(result.first?"ok":"fail")<<'\t'<<result.second<<'\n';
   } else throw std::invalid_argument("invalid command");
  } catch (const std::exception& error) {std::cout<<"error\t"<<error.what()<<'\n';}
  std::cout.flush();
 }
}
