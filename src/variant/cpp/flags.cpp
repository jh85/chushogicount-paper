// See flags.h.
#include "flags.h"

namespace variant {

FlagResult realizableFlags(const Variant& v, const Candidate& cand, const uint8_t* board, bool lanes,
                           std::vector<FlagRealization>* out) {
  FlagResult res;
  const int n = v.n();
  const int bk = v.code(Black, K), bn = v.code(Black, N);
  if (!bn) return res;                                   // no lion in the variant
  bool haveKing = false;
  int lionsB = 0;
  for (int i = 0; i < n; ++i) {
    if (board[i] == bk) haveKing = true;
    if (board[i] == bn) ++lionsB;
  }
  if (!haveKing) return res;                             // terminal: no move follows
  int maxLions = 0;
  for (const Tables::Group& g : cand.tables().groups)
    if (g.colour == Black && g.role == N) maxLions = g.max;
  if (lionsB + 1 > maxLions) return res;                 // I9
  std::vector<Move> moves;
  State P;
  for (int l = 0; l < n; ++l) {
    if (!board[l] || v.colourOf(board[l]) != White) continue;
    Role role = v.roleOf(board[l]);
    // (prior role, promoted on the capture)
    int priors[2][2];
    int np = 0;
    if (!isLion(role)) {
      priors[np][0] = role;
      priors[np][1] = 0;
      ++np;
    }
    for (Role r : v.def().roles)
      if (promotesTo(r) == role && v.code(White, r)) {
        priors[np][0] = r;
        priors[np][1] = 1;
        ++np;
      }
    for (int k = 0; k < np; ++k) {
      Role prior = (Role)priors[k][0];
      bool promoted = priors[k][1] != 0;
      for (int a = 0; a < n; ++a) {
        if (board[a] || a == l) continue;
        for (int i = 0; i < kMaxSquares; ++i) P.board[i] = i < n ? board[i] : 0;
        P.board[l] = (uint8_t)bn;
        P.board[a] = (uint8_t)v.code(White, prior);
        P.turn = White;
        P.flag = kNone;
        if (!cand.isCandidate(P.board)) continue;
        v.legalMoves(P, moves);
        Move want{(int8_t)a, (int8_t)kNone, (int8_t)l, (uint8_t)(promoted ? 1 : 0)};
        bool legal = false;
        for (const Move& m : moves)
          if (m == want) legal = true;
        if (!legal) continue;
        res.acceptedNoLanes |= 1u << l;
        if (lanes && !cand.laneOk(P.board)) continue;
        res.accepted |= 1u << l;
        if (out) out->push_back(FlagRealization{(int8_t)l, (int8_t)a, prior, (uint8_t)(promoted ? 1 : 0)});
      }
    }
  }
  if (!lanes) res.accepted = res.acceptedNoLanes;
  return res;
}

bool flagEffective(const Variant& v, const uint8_t* board, int l, std::vector<Move>& a, std::vector<Move>& b) {
  State s;
  for (int i = 0; i < kMaxSquares; ++i) s.board[i] = i < v.n() ? board[i] : 0;
  s.turn = Black;
  s.flag = (int8_t)l;
  v.legalMoves(s, a);
  s.flag = kNone;
  v.legalMoves(s, b);
  return a.size() != b.size();
}

}  // namespace variant
