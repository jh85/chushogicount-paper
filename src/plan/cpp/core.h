// Planner core: squares, pieces, Python-style repr, move geometry (port of plan/moves.py).
//
// Squares are indices s = x*12 + (r-1), x = 0..11 from Black's left, r = 1..12 from
// Black's side, so index order equals Python's tuple order on (x, r) and SQUARES order.
// A piece is 0 (empty) or 1 + 2*role + colour (colour 0 = Black 'B', 1 = White 'W'),
// roles as in count/sfen.py with kirin/phoenix/elephant promotions identified (N, Q, K).
#pragma once
#include <array>
#include <bitset>
#include <cstdint>
#include <cstdlib>
#include <string>
#include <utility>
#include <vector>

namespace cp {

enum Role : int {
  P, GB, L, RC, M, V, C, S, F, T, G, E, B, R, H, D, O, X, K, N, Q,
  pP, pGB, pL, pRC, pM, pV, pC, pS, pF, pT, pG, pB, pR, pH, pD, NROLES
};
extern const char* const ROLE_NAME[NROLES];
// PROMOTES of plan/moves.py (E -> K, O -> N, X -> Q); -1 if the role does not promote
int promotes(int role);

using Piece = uint8_t;
inline Piece mk(int colour, int role) { return (Piece)(1 + 2 * role + colour); }
inline int colour_of(Piece p) { return (p - 1) & 1; }
inline int role_of(Piece p) { return (p - 1) >> 1; }
inline char colour_ch(int c) { return c == 0 ? 'B' : 'W'; }
inline int other(int c) { return 1 - c; }

inline int SX(int s) { return s / 12; }
inline int SR(int s) { return s % 12 + 1; }
inline int SQ(int x, int r) { return x * 12 + r - 1; }
inline bool on_board(int x, int r) { return 0 <= x && x < 12 && 1 <= r && r <= 12; }
inline int cheb(int a, int b) {
  int dx = std::abs(SX(a) - SX(b)), dy = std::abs(SR(a) - SR(b));
  return dx > dy ? dx : dy;
}
inline int sq_class(int s) { return (SX(s) + SR(s)) % 2; }
inline bool in_zone(int colour, int s) { return colour == 0 ? SR(s) >= 9 : SR(s) <= 4; }

// dict order of a board parsed from an SFEN: ranks 12..1, files a..l
extern const std::array<int, 144> CANON;

using Board = std::array<Piece, 144>;
using SqSet = std::bitset<144>;

// A dict {square: piece} with Python insertion order (targets, relax predecessors).
struct OBoard {
  Board a{};
  std::vector<int> order;
  bool has(int s) const { return a[s] != 0; }
  Piece get(int s) const { return a[s]; }
  void set(int s, Piece p) {
    if (!a[s]) order.push_back(s);
    a[s] = p;
  }
  void erase(int s) {
    if (!a[s]) return;
    a[s] = 0;
    for (size_t i = 0; i < order.size(); ++i)
      if (order[i] == s) { order.erase(order.begin() + i); break; }
  }
};

// ---- Python exceptions -------------------------------------------------------
struct PlannerError {
  std::string phase, reason;
  int at = -1;
  std::string str() const { return phase + ": " + reason; }
};
struct Repetition {
  std::string msg;
};
struct PyExc {                 // any other Python exception the original would raise
  std::string type, msg;
};

// ---- repr ----------------------------------------------------------------------
std::string rsq(int s);                         // "(x, r)"
std::string rpiece(Piece p);                    // "('B', 'N')" or "None"
std::string rsqlist(const std::vector<int>& v); // "[(x, r), ...]"
inline std::string cstr(int c) { return std::string(1, colour_ch(c)); }
[[noreturn]] inline void key_error(int s) { throw PyExc{"KeyError", rsq(s)}; }

// ---- moves (plan/moves.py) -----------------------------------------------------
struct Vec { int dx, dy; };
struct RoleMoves { std::vector<Vec> steps, slides; };
extern std::array<RoleMoves, NROLES> MOVES;
void init_tables();

// Planner move; mid = -1 for an ordinary move.
struct PMove {
  int from = -1, mid = -1, to = -1;
  bool promote = false;
  bool operator==(const PMove& o) const {
    return from == o.from && mid == o.mid && to == o.to && promote == o.promote;
  }
};
inline PMove mv(int frm, int to, bool promote = false, int mid = -1) { return PMove{frm, mid, to, promote}; }
std::string usi_sq(int s);
std::string usi(const PMove& m);

// single_moves / reverse_moves / adjacent_dests over an occupancy getter g(s) -> Piece
template <class Get>
void single_moves(Get g, int sq, Piece piece, std::vector<int>& out) {
  out.clear();
  int colour = colour_of(piece), sign = colour == 0 ? 1 : -1;
  const RoleMoves& m = MOVES[role_of(piece)];
  int x = SX(sq), r = SR(sq);
  for (const Vec& d : m.steps) {
    int tx = x + d.dx, tr = r + d.dy * sign;
    if (!on_board(tx, tr)) continue;
    Piece q = g(SQ(tx, tr));
    if (!q || colour_of(q) != colour) out.push_back(SQ(tx, tr));
  }
  for (const Vec& d : m.slides) {
    int tx = x + d.dx, tr = r + d.dy * sign;
    while (on_board(tx, tr)) {
      Piece q = g(SQ(tx, tr));
      if (q) {
        if (colour_of(q) != colour) out.push_back(SQ(tx, tr));
        break;
      }
      out.push_back(SQ(tx, tr));
      tx += d.dx;
      tr += d.dy * sign;
    }
  }
}

template <class Get>
void reverse_moves(Get g, int sq, Piece piece, std::vector<int>& out) {
  out.clear();
  int sign = colour_of(piece) == 0 ? 1 : -1;
  const RoleMoves& m = MOVES[role_of(piece)];
  int x = SX(sq), r = SR(sq);
  for (const Vec& d : m.steps) {
    int tx = x - d.dx, tr = r - d.dy * sign;
    if (on_board(tx, tr) && !g(SQ(tx, tr))) out.push_back(SQ(tx, tr));
  }
  for (const Vec& d : m.slides) {
    int tx = x - d.dx, tr = r - d.dy * sign;
    while (on_board(tx, tr) && !g(SQ(tx, tr))) {
      out.push_back(SQ(tx, tr));
      tx -= d.dx;
      tr -= d.dy * sign;
    }
  }
}

void adjacent_dests(int sq, Piece piece, std::vector<int>& out);
// squares strictly between a and b crossed by a sliding move (empty for steps/jumps)
std::vector<int> traversed(Piece piece, int a, int b);

// BFS path through empty squares (plan/moves.py path); board[sq] must be a piece.
bool path(const Board& board, int sq, const SqSet& goals, const SqSet& walls, bool capture,
          std::vector<int>& out);

}  // namespace cp
