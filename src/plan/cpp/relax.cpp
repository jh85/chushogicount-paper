#include "relax.h"

#include <algorithm>
#include <unordered_set>

#include "filegame.h"
#include "planner.h"

namespace cp {

PMove parse_usi(const std::string& s) {
  PMove m;
  std::vector<int> sqs;
  size_t i = 0;
  while (i < s.size() && s[i] != '+') {
    int f = 0;
    while (i < s.size() && isdigit((unsigned char)s[i])) f = f * 10 + (s[i++] - '0');
    int letter = s[i++] - 'a';
    sqs.push_back(SQ(12 - f, 12 - letter));
  }
  m.promote = !s.empty() && s.back() == '+';
  m.from = sqs[0];
  if (sqs.size() == 3) {
    m.mid = sqs[1];
    m.to = sqs[2];
  } else {
    m.to = sqs[1];
  }
  return m;
}

bool certify(const std::vector<std::string>& moves, const OBoard& target, int turn, Eng& eng, std::string* why) {
  auto fail = [&](const std::string& w) {
    if (why) *why = w;
    return false;
  };
  eng.set_board(target.a, turn);
  chu::GameEnd target_status = chu::evaluateStatus(eng.pos()).end;
  eng.set_initial();
  std::unordered_set<StateKey, StateKeyHash> seen;
  Board b;
  int side, flag;
  for (size_t i = 0; i < moves.size(); ++i) {
    eng.state(b, side, flag);
    StateKey k;
    std::copy(b.begin(), b.end(), k.k.begin());
    k.k[144] = (uint8_t)side;
    k.k[145] = (uint8_t)(flag + 1);
    if (seen.count(k)) return fail("repetition before ply " + std::to_string(i));
    seen.insert(k);
    PMove m = parse_usi(moves[i]);
    if (!eng.is_legal(m)) return fail("illegal move " + moves[i] + " at ply " + std::to_string(i));
    if (i > 0 && !eng.playing()) return fail("terminal position before ply " + std::to_string(i));
    eng.move(m);
  }
  eng.state(b, side, flag);
  if (side != turn) return fail("side to move");
  if (flag != -1) return fail("final flag");
  if (b != target.a) return fail("final board differs from the target");
  if (chu::evaluateStatus(eng.pos()).end != target_status) return fail("final status");
  if (why) *why = std::to_string(moves.size()) + " plies";
  return true;
}

static int pocket_score(const OBoard& board) {
  int score = 0;
  std::vector<int> ts;
  for (int sq : board.order) {
    Piece piece = board.a[sq];
    int role = role_of(piece);
    if (role == P || role == L) continue;
    Board b = board.a;
    b[sq] = 0;
    SqSet region;
    region.set(sq);
    int count = 1;
    std::vector<int> stack{sq};
    while (!stack.empty() && count < 12) {
      int cur = stack.back();
      stack.pop_back();
      reverse_moves([&](int t) { return b[t]; }, cur, piece, ts);
      for (int t : ts)
        if (!region[t]) {
          region.set(t);
          ++count;
          stack.push_back(t);
        }
    }
    score += 12 - count;
  }
  return score;
}

struct Digest {
  uint64_t a, b;
  bool operator==(const Digest& o) const { return a == o.a && b == o.b; }
};
struct DigestHash {
  size_t operator()(const Digest& d) const { return (size_t)(d.a ^ (d.b * 0x9e3779b97f4a7c15ULL)); }
};
static Digest digest(const Board& b) {
  uint64_t h1 = 1469598103934665603ULL, h2 = 0x6a09e667f3bcc909ULL;
  for (int i = 0; i < 144; ++i) {
    h1 = (h1 ^ b[i]) * 1099511628211ULL;
    h2 = (h2 + b[i] + 1) * 0xff51afd7ed558ccdULL;
    h2 ^= h2 >> 29;
  }
  return {h1, h2};
}

struct Node {
  int score;
  OBoard board;
  int turn;
  std::vector<std::string> fwd;
};

bool relax(const OBoard& target, Eng& eng, int depth, int beam, int tries, int planner_retries, int turn,
           std::vector<std::string>& out, RelaxInfo& info, bool fix_turn) {
  info = RelaxInfo();
  int base = pocket_score(target);
  std::vector<Node> frontier{{base, target, turn, {}}};
  std::unordered_set<Digest, DigestHash> seen{digest(target.a)};
  std::vector<int> ts;
  int cert_turn = turn;
  for (int level = 1; level <= depth; ++level) {
    if (!fix_turn) cert_turn = frontier.back().turn;    // the shadowed `turn` of relax.py
    std::vector<Node> cands;
    for (const Node& nd : frontier) {
      int mover = other(nd.turn);
      for (int sq : std::vector<int>(nd.board.order)) {
        Piece piece = nd.board.a[sq];
        if (colour_of(piece) != mover) continue;
        OBoard b = nd.board;
        b.erase(sq);
        std::vector<int> origins;
        reverse_moves([&](int t) { return b.a[t]; }, sq, piece, origins);
        for (int a : origins) {
          OBoard pb = b;
          pb.set(a, piece);
          if (!is_candidate_primary(pb.a)) continue;
          PMove m = mv(a, sq);
          eng.set_board(pb.a, mover);
          if (!eng.is_legal(m) || !eng.playing()) continue;
          Digest d = digest(pb.a);
          if (seen.count(d)) continue;
          seen.insert(d);
          std::vector<std::string> fwd{usi(m)};
          fwd.insert(fwd.end(), nd.fwd.begin(), nd.fwd.end());
          cands.push_back({pocket_score(pb), pb, mover, std::move(fwd)});
        }
      }
    }
    if (cands.empty()) break;
    std::stable_sort(cands.begin(), cands.end(), [](const Node& x, const Node& y) { return x.score < y.score; });
    if ((int)cands.size() > beam) cands.resize(beam);
    frontier = std::move(cands);
    info.levels = level;
    for (int k = 0; k < (int)frontier.size() && k < tries; ++k) {
      const Node& nd = frontier[k];
      if (nd.score >= base) continue;
      info.tried++;
      for (int attempt = 0; attempt < planner_retries; ++attempt) {
        std::vector<std::string> moves;
        try {
          Planner pl(nd.board, eng, attempt, nd.turn, attempt % 2 == 0 ? Strategy::Greedy : Strategy::Peel, false,
                     false);
          moves = pl.run();
        } catch (...) {
          continue;
        }
        moves.insert(moves.end(), nd.fwd.begin(), nd.fwd.end());
        if (certify(moves, target, cert_turn, eng)) {
          info.ok = true;
          info.retracted = (int)nd.fwd.size();
          info.plies = (int)moves.size();
          info.base = base;
          info.score = nd.score;
          out = moves;
          return true;
        }
      }
    }
  }
  info.ok = false;
  return false;
}

}  // namespace cp
