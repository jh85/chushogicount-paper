#include "core.h"

#include <algorithm>

namespace cp {

const char* const ROLE_NAME[NROLES] = {
    "P", "GB", "L", "RC", "M", "V", "C", "S", "F", "T", "G", "E", "B", "R", "H", "D", "O", "X",
    "K", "N", "Q", "+P", "+GB", "+L", "+RC", "+M", "+V", "+C", "+S", "+F", "+T", "+G", "+B",
    "+R", "+H", "+D"};

int promotes(int role) {
  switch (role) {
    case P: return pP; case GB: return pGB; case L: return pL; case RC: return pRC;
    case M: return pM; case V: return pV; case C: return pC; case S: return pS;
    case F: return pF; case T: return pT; case G: return pG; case E: return K;
    case B: return pB; case R: return pR; case H: return pH; case D: return pD;
    case O: return N; case X: return Q;
    default: return -1;
  }
}

static std::array<int, 144> make_canon() {
  std::array<int, 144> c{};
  int k = 0;
  for (int r = 12; r >= 1; --r)
    for (int x = 0; x < 12; ++x) c[k++] = SQ(x, r);
  return c;
}
const std::array<int, 144> CANON = make_canon();

std::string rsq(int s) { return "(" + std::to_string(SX(s)) + ", " + std::to_string(SR(s)) + ")"; }
std::string rpiece(Piece p) {
  if (!p) return "None";
  return std::string("('") + colour_ch(colour_of(p)) + "', '" + ROLE_NAME[role_of(p)] + "')";
}
std::string rsqlist(const std::vector<int>& v) {
  std::string s = "[";
  for (size_t i = 0; i < v.size(); ++i) s += (i ? ", " : "") + rsq(v[i]);
  return s + "]";
}

std::array<RoleMoves, NROLES> MOVES;

void init_tables() {
  const Vec Nn{0, 1}, Ss{0, -1}, Ee{1, 0}, Ww{-1, 0}, NE{1, 1}, NW{-1, 1}, SE{1, -1}, SW{-1, -1};
  const std::vector<Vec> ORTH{Nn, Ss, Ee, Ww}, DIAG{NE, NW, SE, SW};
  std::vector<Vec> ALL = ORTH;
  ALL.insert(ALL.end(), DIAG.begin(), DIAG.end());
  auto J = [](Vec d) { return Vec{2 * d.dx, 2 * d.dy}; };
  auto cat = [](std::vector<Vec> a, const std::vector<Vec>& b) {
    a.insert(a.end(), b.begin(), b.end());
    return a;
  };
  auto except = [&](Vec e) {
    std::vector<Vec> o;
    for (Vec d : ALL)
      if (!(d.dx == e.dx && d.dy == e.dy)) o.push_back(d);
    return o;
  };
  std::vector<Vec> lion;
  for (int dx = -2; dx <= 2; ++dx)
    for (int dy = -2; dy <= 2; ++dy)
      if (dx || dy) lion.push_back({dx, dy});
  std::vector<Vec> jo, jd;
  for (Vec d : ORTH) jo.push_back(J(d));
  for (Vec d : DIAG) jd.push_back(J(d));
  MOVES[P] = {{Nn}, {}};
  MOVES[GB] = {{Nn, Ss}, {}};
  MOVES[L] = {{}, {Nn}};
  MOVES[RC] = {{}, {Nn, Ss}};
  MOVES[M] = {{Nn, Ss}, {Ee, Ww}};
  MOVES[V] = {{Ee, Ww}, {Nn, Ss}};
  MOVES[C] = {{Nn, NE, NW, Ss}, {}};
  MOVES[S] = {{Nn, NE, NW, SE, SW}, {}};
  MOVES[F] = {cat({Nn, Ss}, DIAG), {}};
  MOVES[T] = {except(Nn), {}};
  MOVES[G] = {{Nn, Ss, Ee, Ww, NE, NW}, {}};
  MOVES[E] = {except(Ss), {}};
  MOVES[B] = {{}, DIAG};
  MOVES[R] = {{}, ORTH};
  MOVES[H] = {ORTH, DIAG};
  MOVES[D] = {DIAG, ORTH};
  MOVES[O] = {cat(DIAG, jo), {}};
  MOVES[X] = {cat(ORTH, jd), {}};
  MOVES[K] = {ALL, {}};
  MOVES[N] = {lion, {}};
  MOVES[Q] = {{}, ALL};
  MOVES[pL] = {{}, {Nn, Ss, NE, NW}};
  MOVES[pRC] = {{}, {Nn, Ss, SE, SW}};
  MOVES[pM] = {{}, cat({Ee, Ww}, DIAG)};
  MOVES[pV] = {{}, cat({Nn, Ss}, DIAG)};
  MOVES[pT] = {cat({Ee, Ww}, DIAG), {Nn, Ss}};
  MOVES[pH] = {{Nn, J(Nn)}, except(Nn)};
  MOVES[pD] = {{NE, NW, J(NE), J(NW)}, {Nn, Ss, Ee, Ww, SE, SW}};
  MOVES[pP] = MOVES[G];
  MOVES[pGB] = MOVES[E];
  MOVES[pC] = MOVES[M];
  MOVES[pS] = MOVES[V];
  MOVES[pF] = MOVES[B];
  MOVES[pG] = MOVES[R];
  MOVES[pB] = MOVES[H];
  MOVES[pR] = MOVES[D];
}

std::string usi_sq(int s) {
  static const char* RANKS = "abcdefghijkl";
  return std::to_string(12 - SX(s)) + RANKS[12 - SR(s)];
}

std::string usi(const PMove& m) {
  std::string s = usi_sq(m.from);
  if (m.mid >= 0) s += usi_sq(m.mid);
  s += usi_sq(m.to);
  if (m.promote) s += '+';
  return s;
}

void adjacent_dests(int sq, Piece piece, std::vector<int>& out) {
  out.clear();
  int sign = colour_of(piece) == 0 ? 1 : -1;
  const RoleMoves& m = MOVES[role_of(piece)];
  for (const auto* lst : {&m.steps, &m.slides})
    for (const Vec& d : *lst) {
      int tx = SX(sq) + d.dx, tr = SR(sq) + d.dy * sign;
      if (on_board(tx, tr)) out.push_back(SQ(tx, tr));
    }
}

static int floordiv(int a, int b) {
  int q = a / b;
  if ((a % b != 0) && ((a < 0) != (b < 0))) --q;
  return q;
}

std::vector<int> traversed(Piece piece, int a, int b) {
  int sign = colour_of(piece) == 0 ? 1 : -1;
  int dx = SX(b) - SX(a), dy = (SR(b) - SR(a)) * sign;
  const RoleMoves& m = MOVES[role_of(piece)];
  for (const Vec& d : m.steps)
    if (d.dx == dx && d.dy == dy) return {};
  int n = std::max(std::abs(dx), std::abs(dy));
  if (n <= 1) return {};
  int ux = floordiv(dx, n), uy = floordiv(dy, n);
  std::vector<int> out;
  for (int i = 1; i < n; ++i) out.push_back(SQ(SX(a) + ux * i, SR(a) + uy * sign * i));
  return out;
}

bool path(const Board& board, int sq, const SqSet& goals, const SqSet& walls, bool capture,
          std::vector<int>& out) {
  if (!board[sq]) key_error(sq);
  Piece piece = board[sq];
  int colour = colour_of(piece);
  std::array<int16_t, 144> prev;
  prev.fill(-2);
  prev[sq] = -1;
  int nprev = 1;
  std::vector<int> q{sq}, moves;
  size_t head = 0;
  while (head < q.size()) {
    int cur = q[head++];
    if (goals[cur] && cur != sq) {
      out.clear();
      while (cur != sq) {
        out.push_back(cur);
        cur = prev[cur];
      }
      std::reverse(out.begin(), out.end());
      return true;
    }
    if (nprev > 2000) break;
    auto g = [&](int t) -> Piece { return t == cur ? piece : (t == sq ? 0 : board[t]); };
    single_moves(g, cur, piece, moves);
    for (int t : moves) {
      if (prev[t] != -2 || walls[t]) continue;
      Piece o = g(t);
      if (o) {
        if (capture && goals[t] && colour_of(o) != colour) {
          prev[t] = (int16_t)cur;
          ++nprev;
          q.push_back(t);
        }
        continue;
      }
      prev[t] = (int16_t)cur;
      ++nprev;
      q.push_back(t);
    }
  }
  return false;
}

}  // namespace cp
