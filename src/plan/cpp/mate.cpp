#include "mate.h"

#include <algorithm>
#include <array>
#include <cstdlib>

#include "eng.h"
#include "../../../out/engine/src/movegen.h"
#include "../../../out/engine/src/usi.h"

namespace cp {

static bool royal_of(uint8_t p, chu::Color c) {
  return p && chu::colorOf(p) == c && chu::isRoyal(chu::roleOf(p));
}

// The reference: some legal move of the opponent (no flag) captures a royal of side.
static bool royal_capturable_gen(const chu::Position& pos, chu::Color side, chu::RuleSet rules) {
  chu::Position q = pos;
  q.sideToMove = !side;
  q.lastLionCapture = chu::kNoSquare;
  q.rules = rules;
  for (const chu::Move& m : chu::generateLegal(q)) {
    if (royal_of(q.board[m.to], side)) return true;
    if (m.mid != chu::kNoSquare && royal_of(q.board[m.mid], side)) return true;
  }
  return false;
}

// The same through the planner's move tables (single_moves: steps, slides, the lion's,
// kirin's, phoenix's, horned falcon's and soaring eagle's jumps): the lion-trading rules,
// the only restrictions beyond geometry, never forbid capturing a royal, and a double move
// captures on its mid square or on a square its single moves reach.  Checked against
// royal_capturable_gen through tests/test_cmate.py (CHU_PLAN_MATE_REF=1 selects the reference).
static const bool kRef = std::getenv("CHU_PLAN_MATE_REF") != nullptr;
// D13 as first worded (pilot P1): a promotion to a prince is not an escape (D13a: it is).
static const bool kD13Original = std::getenv("CHU_PLAN_D13_ORIGINAL") != nullptr;
// D13 before D13b (pilots P2, P3, run G13): a capture of the opponent's last royal is not an
// escape (D13b: it is, since it ends the game).
static const bool kD13ReadingA = std::getenv("CHU_PLAN_D13_READING_A") != nullptr;

bool royal_capturable(const chu::Position& pos, chu::Color side, chu::RuleSet rules) {
  if (kRef) return royal_capturable_gen(pos, side, rules);
  Board b;
  b.fill(0);
  bool any = false;
  for (int e = 0; e < chu::kSquares; ++e)
    if (pos.board[e]) {
      b[from_esq(e)] = from_epiece(pos.board[e]);
      any |= royal_of(pos.board[e], side);
    }
  if (!any) return false;
  auto g = [&](int s) { return b[s]; };
  std::vector<int> out;
  for (int e = 0; e < chu::kSquares; ++e) {
    uint8_t p = pos.board[e];
    if (!p || chu::colorOf(p) == side) continue;
    int s = from_esq(e);
    single_moves(g, s, b[s], out);
    for (int t : out)
      if (royal_of(pos.board[to_esq(t)], side)) return true;
  }
  return false;
}

// D13a: after a promotion to a prince, can the opponent (no flag) capture king and prince in
// one move (a double move capturing on its mid square and its destination)?
static bool both_royals_capturable(const chu::Position& pos, chu::Color side) {
  chu::Position q = pos;
  q.sideToMove = !side;
  q.lastLionCapture = chu::kNoSquare;
  for (const chu::Move& m : chu::generateLegal(q))
    if (m.mid != chu::kNoSquare && royal_of(q.board[m.to], side) && royal_of(q.board[m.mid], side)) return true;
  return false;
}

// Engine squares a defender move must touch to stop an attack on the royal on engine square
// re: every attacker's square and the squares strictly inside its slide to the royal.  A move
// that does not move the royal and neither lands on nor captures (mid square) such a square
// leaves every attack in place (vacating a square only opens lines), so the royal stays
// capturable without a full test.
static std::array<char, chu::kSquares> hot_squares(const chu::Position& p, int re) {
  std::array<char, chu::kSquares> hot{};
  Board b;
  b.fill(0);
  for (int e = 0; e < chu::kSquares; ++e)
    if (p.board[e]) b[from_esq(e)] = from_epiece(p.board[e]);
  auto g = [&](int s) { return b[s]; };
  const int r = from_esq(re);
  std::vector<int> out;
  for (int e = 0; e < chu::kSquares; ++e) {
    uint8_t q = p.board[e];
    if (!q || chu::colorOf(q) == p.sideToMove) continue;
    int s = from_esq(e);
    single_moves(g, s, b[s], out);
    if (std::find(out.begin(), out.end(), r) == out.end()) continue;
    hot[e] = 1;
    for (int t : traversed(b[s], s, r)) hot[to_esq(t)] = 1;
  }
  return hot;
}

bool mated(const chu::Position& pos, chu::RuleSet rules) {
  chu::Position p = pos;
  p.rules = rules;
  const chu::Color stm = p.sideToMove;
  int royals = 0, re = -1;
  for (int s = 0; s < chu::kSquares; ++s)
    if (royal_of(p.board[s], stm)) ++royals, re = s;
  if (royals != 1 || !royal_capturable(p, stm, rules)) return false;
  std::array<char, chu::kSquares> hot{};
  if (!kRef) hot = hot_squares(p, re);
  int opp_royals = 0;
  for (int s = 0; s < chu::kSquares; ++s) opp_royals += royal_of(p.board[s], !stm);
  for (const chu::Move& m : chu::generateLegal(p)) {
    if (!kD13ReadingA && (royal_of(p.board[m.to], !stm) || (m.mid != chu::kNoSquare && royal_of(p.board[m.mid], !stm)))) {
      int taken = royal_of(p.board[m.to], !stm) + (m.mid != chu::kNoSquare && royal_of(p.board[m.mid], !stm));
      if (taken == opp_royals) return false;        // D13b: the opponent's last royal(s) captured
    }
    const bool prince = m.promote && chu::roleOf(p.board[m.from]) == chu::Elephant;
    if (prince && !kD13Original) {                  // D13a: a second royal
      chu::Position q = p;
      q.apply(m);
      if (!both_royals_capturable(q, stm)) return false;
      continue;
    }
    if (!kRef && m.from != re && !hot[m.to] && (m.mid == chu::kNoSquare || !hot[m.mid])) continue;
    chu::Position q = p;
    q.apply(m);
    if (!royal_capturable(q, stm, rules)) return false;
  }
  return true;
}

static bool strict_safe(const chu::Position& p) {
  if (mated(p)) return false;
  chu::Position q = p;
  q.sideToMove = !q.sideToMove;
  q.lastLionCapture = chu::kNoSquare;
  return !mated(q);
}

// The position after the USI move s, if it is among `legal` (generateLegal(p)) and safe.
static bool step(const chu::Position& p, const std::vector<chu::Move>& legal, const std::string& s,
                 chu::Position& out) {
  chu::Move m;
  if (!chu::parseUsiMove(s, m)) return false;
  bool found = false;
  for (const chu::Move& g : legal)
    if (g.from == m.from && g.mid == m.mid && g.to == m.to && g.promote == m.promote) found = true;
  if (!found) return false;
  out = p;
  out.apply(m);
  return strict_safe(out);
}

std::vector<std::pair<int, int>> fix_pairs(const chu::Position& pos, const std::string& mv,
                                           const std::vector<std::string>& as,
                                           const std::vector<std::vector<std::string>>& bs, int k) {
  std::vector<std::pair<int, int>> out;
  chu::Position pa, pb, pm;
  const std::vector<chu::Move> la = chu::generateLegal(pos);
  for (size_t i = 0; i < as.size(); ++i) {
    if (!step(pos, la, as[i], pa)) continue;
    const std::vector<chu::Move> lb = chu::generateLegal(pa);
    for (size_t j = 0; j < bs[i].size(); ++j) {
      if (!step(pa, lb, bs[i][j], pb) || !step(pb, chu::generateLegal(pb), mv, pm)) continue;
      out.emplace_back((int)i, (int)j);
      if ((int)out.size() >= k) return out;
    }
  }
  return out;
}

std::vector<int> mate_plies(const std::vector<std::string>& moves, int* illegal) {
  Eng eng;
  eng.set_initial();
  chu::Position p = eng.pos();
  p.rules = chu::RuleSet::JCSA;
  std::vector<int> out;
  *illegal = -1;
  for (size_t i = 0; i <= moves.size(); ++i) {
    if (mated(p)) out.push_back((int)i);
    if (i == moves.size()) break;
    chu::Move m;
    if (!chu::parseUsiMove(moves[i], m) || !chu::isLegal(p, m)) {
      *illegal = (int)i;
      break;
    }
    p.apply(m);
  }
  return out;
}

}  // namespace cp
