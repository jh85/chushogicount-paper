// See variant.h.  Line-by-line port of src/variant/rules.py; comments name the
// Python function each block corresponds to.
#include "variant.h"

#include <algorithm>
#include <cstdio>
#include <cstdlib>

namespace variant {

const char* const kRoleName[RoleCount] = {"K", "N", "P", "L", "GB", "B", "+P", "+L", "+GB", "+B", "E", "O"};
const char* const kStatusName[StatusCount] = {"playing", "royalslost", "bareking", "stalemate", "draw"};

void die(const std::string& msg) {
  std::fprintf(stderr, "fatal: %s\n", msg.c_str());
  std::exit(2);
}

int roleByName(const std::string& name) {
  for (int r = 0; r < RoleCount; ++r)
    if (name == kRoleName[r]) return r;
  return -1;
}

int promotesTo(Role r) {              // plan.moves.PROMOTES restricted to these roles
  switch (r) {
    case P: return PP;
    case L: return PL;
    case GB: return PGB;
    case B: return PB;
    case E: return K;
    case O: return N;
    default: return -1;
  }
}

int unpromotedForm(Role r) {          // plan.lanes.UNPROMOTED
  switch (r) {
    case PP: return P;
    case PL: return L;
    case PGB: return GB;
    case PB: return B;
    case K: return E;
    case N: return O;
    default: return -1;
  }
}

bool isConfinedKind(Role r) { return r == P || r == L || r == GB; }

namespace {

const Dir DN{0, 1}, DS{0, -1}, DE{1, 0}, DW{-1, 0}, DNE{1, 1}, DNW{-1, 1}, DSE{1, -1}, DSW{-1, -1};
const std::vector<Dir> ORTH{DN, DS, DE, DW}, DIAG{DNE, DNW, DSE, DSW};
const std::vector<Dir> ALL{DN, DS, DE, DW, DNE, DNW, DSE, DSW};

std::vector<Dir> cat(const std::vector<Dir>& a, const std::vector<Dir>& b) {
  std::vector<Dir> out(a);
  out.insert(out.end(), b.begin(), b.end());
  return out;
}

std::vector<Dir> allExcept(Dir d) {
  std::vector<Dir> out;
  for (const Dir& e : ALL)
    if (e.dx != d.dx || e.dy != d.dy) out.push_back(e);
  return out;
}

std::vector<Dir> lionSteps() {        // [(dx, dy) for dx in -2..2 for dy in -2..2 if != (0, 0)]
  std::vector<Dir> out;
  for (int dx = -2; dx <= 2; ++dx)
    for (int dy = -2; dy <= 2; ++dy)
      if (dx || dy) out.push_back(Dir{(int8_t)dx, (int8_t)dy});
  return out;
}

const MoveTable kTables[RoleCount] = {
    /* K   */ {ALL, {}},
    /* N   */ {lionSteps(), {}},
    /* P   */ {{DN}, {}},
    /* L   */ {{}, {DN}},
    /* GB  */ {{DN, DS}, {}},
    /* B   */ {{}, DIAG},
    /* +P  */ {{DN, DS, DE, DW, DNE, DNW}, {}},                   // gold
    /* +L  */ {{}, {DN, DS, DNE, DNW}},
    /* +GB */ {allExcept(DS), {}},                               // drunk elephant
    /* +B  */ {ORTH, DIAG},                                      // dragon horse
    /* E   */ {allExcept(DS), {}},
    /* O   */ {cat(DIAG, {Dir{0, 2}, Dir{0, -2}, Dir{2, 0}, Dir{-2, 0}}), {}},
};

}  // namespace

const MoveTable& moveTable(Role r) { return kTables[r]; }

// ---- the variants of src/variant/bfs.py ------------------------------------
namespace {

std::vector<Def> makeDefs() {
  std::vector<Def> v;
  // V1: 3x5, zone 1.  Black: L a1, N b1, K c1, P b2.  White: rotated 180 degrees.
  v.push_back(Def{"V1", 3, 5, 1, {K, N, P, L, PP, PL},
                  {{0, 1, Black, L}, {1, 1, Black, N}, {2, 1, Black, K}, {1, 2, Black, P},
                   {2, 5, White, L}, {1, 5, White, N}, {0, 5, White, K}, {1, 4, White, P}}});
  // V8: pawn + go-between + lion + king.  Black: GB a2, N b1, K c1, P b2.
  v.push_back(Def{"V8", 3, 5, 1, {K, N, P, GB, PP, PGB},
                  {{0, 2, Black, GB}, {1, 1, Black, N}, {2, 1, Black, K}, {1, 2, Black, P},
                   {2, 4, White, GB}, {1, 5, White, N}, {0, 5, White, K}, {1, 4, White, P}}});
  // V6: lance + pawn + one colour-bound bishop + king (no lion).  Black: L a1, B b1, K c1, P b2.
  v.push_back(Def{"V6", 3, 5, 1, {K, B, P, L, PP, PL, PB},
                  {{0, 1, Black, L}, {1, 1, Black, B}, {2, 1, Black, K}, {1, 2, Black, P},
                   {2, 5, White, L}, {1, 5, White, B}, {0, 5, White, K}, {1, 4, White, P}}});
  return v;
}

const std::vector<Def>& defs() {
  static const std::vector<Def> d = makeDefs();
  return d;
}

}  // namespace

const Def* findVariant(const std::string& name) {
  for (const Def& d : defs())
    if (d.name == name) return &d;
  return nullptr;
}

std::vector<std::string> variantNames() {
  std::vector<std::string> out;
  for (const Def& d : defs()) out.push_back(d.name);
  return out;
}

// ---- Variant ------------------------------------------------------------------
Variant::Variant(const Def& def) : def_(def), nf_(def.nfiles), nr_(def.nranks), zone_(def.zone) {
  n_ = nf_ * nr_;
  if (n_ > kMaxSquares) die("board too large for the packing");
  for (int c = 0; c < 2; ++c)
    for (int r = 0; r < RoleCount; ++r) code_[c][r] = 0;
  for (int c = 0; c < 2; ++c)
    for (Role r : def.roles) {
      if (code_[c][r]) die("duplicate role in the variant definition");
      pieces_.push_back(Piece{(Colour)c, r});
      code_[c][r] = (int)pieces_.size();
    }
  // packing capacity: (npieces+1)^n * 2 * (n+1) must fit in 64 bits
  {
    long double cap = 1;
    for (int i = 0; i < n_; ++i) cap *= npieces() + 1;
    cap *= 2 * (n_ + 1);
    if (cap >= 18446744073709551616.0L) die("state does not fit in 64 bits");
  }
  for (int i = 0; i < kMaxSquares; ++i) start_.board[i] = 0;
  for (const StartPiece& p : def.start) {
    int i = idx(p.x, p.r);
    if (p.x < 0 || p.x >= nf_ || p.r < 1 || p.r > nr_ || start_.board[i]) die("bad start piece");
    start_.board[i] = (uint8_t)code_[p.colour][p.role];
  }
  start_.turn = Black;
  start_.flag = kNone;
  for (int i = 0; i < n_; ++i)
    for (int j = 0; j < n_; ++j) {
      int dx = fileOf(i) - fileOf(j), dr = rankOf(i) - rankOf(j);
      dist_[i][j] = std::max(std::abs(dx), std::abs(dr));
    }
  // move geometry per (colour, role, square), in the Python table order
  geo_.resize(2 * RoleCount * n_);
  att_.resize(2 * RoleCount * n_ * n_);
  for (int c = 0; c < 2; ++c) {
    int sign = c == Black ? 1 : -1;
    for (int r = 0; r < RoleCount; ++r) {
      const MoveTable& t = kTables[r];
      for (int i = 0; i < n_; ++i) {
        Geo& g = geo_[((int)c * RoleCount + r) * n_ + i];
        int x = fileOf(i), rk = rankOf(i);
        for (const Dir& d : t.steps) {
          int tx = x + d.dx, tr = rk + d.dy * sign;
          if (tx >= 0 && tx < nf_ && tr >= 1 && tr <= nr_) {
            int j = idx(tx, tr);
            g.steps.push_back((uint8_t)j);
            att_[(((int)c * RoleCount + r) * n_ + i) * n_ + j].kind = 1;
          }
        }
        for (const Dir& d : t.slides) {
          std::vector<uint8_t> ray;
          int tx = x + d.dx, tr = rk + d.dy * sign;
          while (tx >= 0 && tx < nf_ && tr >= 1 && tr <= nr_) {
            int j = idx(tx, tr);
            Att& a = att_[(((int)c * RoleCount + r) * n_ + i) * n_ + j];
            if (a.kind == 0) {        // a step takes precedence (attacks() tests steps first)
              a.kind = 2;
              a.path = ray;
            }
            ray.push_back((uint8_t)j);
            tx += d.dx;
            tr += d.dy * sign;
          }
          g.rays.push_back(ray);
        }
      }
    }
  }
}

// rules.py attacks(): can the piece on i capture on j; rem squares count as empty.
bool Variant::attacks(const uint8_t* board, int i, int j, int rem1, int rem2) const {
  Piece p = piece(board[i]);
  const Att& a = att(p.colour, p.role, i, j);
  if (a.kind == 1) return true;
  if (a.kind == 0) return false;
  for (uint8_t k : a.path)
    if (board[k] && k != rem1 && k != rem2) return false;
  return true;
}

// rules.py threatened()
bool Variant::threatened(const uint8_t* board, Colour by, int j, bool pawnsOnly, int rem1, int rem2) const {
  for (int i = 0; i < n_; ++i) {
    if (i == rem1 || i == rem2 || !board[i]) continue;
    Piece p = piece(board[i]);
    if (p.colour != by) continue;
    if (pawnsOnly && p.role != P && p.role != GB) continue;
    if (attacks(board, i, j, rem1, rem2)) return true;
  }
  return false;
}

// rules.py in_check(): any K of colour attacked by the other side
bool Variant::inCheck(const uint8_t* board, Colour c) const {
  int kc = code_[c][K];
  for (int i = 0; i < n_; ++i)
    if (board[i] == kc && threatened(board, other(c), i, false, kNone, kNone)) return true;
  return false;
}

// rules.py can_promote()
bool Variant::canPromote(Role role, Colour c, int i, int j, bool capture) const {
  if (promotesTo(role) < 0) return false;
  int ri = rankOf(i), rj = rankOf(j);
  if (inZone(c, rj) && !inZone(c, ri)) return true;
  if (capture && (inZone(c, rj) || inZone(c, ri))) return true;
  return (role == P || role == L) && rj == lastRank(c);
}

// rules.py legal_moves(), same move order
void Variant::legalMoves(const State& s, std::vector<Move>& out) const {
  out.clear();
  const uint8_t* board = s.board;
  Colour us = s.turn, them = other(us);
  int shortBuf[32], destBuf[32];
  for (int i = 0; i < n_; ++i) {
    if (!board[i] || colourOf(board[i]) != us) continue;
    Role role = roleOf(board[i]);
    const Geo& g = geo(us, role, i);
    int ns = 0, nd = 0;
    for (uint8_t j : g.steps)
      if (!board[j] || colourOf(board[j]) != us) shortBuf[ns++] = j;
    for (const std::vector<uint8_t>& ray : g.rays)
      for (uint8_t j : ray) {
        if (board[j]) {
          if (colourOf(board[j]) != us) destBuf[nd++] = j;
          break;
        }
        destBuf[nd++] = j;
      }
    bool lion = isLion(role);
    for (int t = 0; t < ns + nd; ++t) {
      int j = t < ns ? shortBuf[t] : destBuf[t - ns];
      uint8_t occ = board[j];
      bool occLion = occ && isLion(roleOf(occ));
      if (lion) {
        if (occLion && dist(i, j) > 1 && threatened(board, them, j, false, i, kNone)) continue;   // L1
      } else if (s.flag != kNone && j != s.flag && occLion) {
        continue;                                                                               // L3
      }
      out.push_back(Move{(int8_t)i, (int8_t)kNone, (int8_t)j, 0});
      if (canPromote(role, us, i, j, occ != 0)) out.push_back(Move{(int8_t)i, (int8_t)kNone, (int8_t)j, 1});
    }
    if (!lion) continue;
    for (int a = 0; a < ns; ++a) {
      int m = shortBuf[a];
      if (dist(i, m) != 1) continue;
      out.push_back(Move{(int8_t)i, (int8_t)m, (int8_t)i, 0});                  // igui or jitto
      for (int b = 0; b < ns; ++b) {
        int j = shortBuf[b];
        if (dist(j, m) != 1) continue;
        uint8_t occ = board[j];
        if (!occ || dist(j, i) == 1 || !isLion(roleOf(occ))) {
          out.push_back(Move{(int8_t)i, (int8_t)m, (int8_t)j, 0});
          continue;
        }
        uint8_t mid = board[m];
        bool substantial = mid && roleOf(mid) != P && roleOf(mid) != GB;         // L2
        if (substantial || (!threatened(board, them, j, false, i, m) && !threatened(board, them, j, true, i, kNone)))
          out.push_back(Move{(int8_t)i, (int8_t)m, (int8_t)j, 0});
      }
    }
  }
}

// rules.py apply()
State Variant::apply(const State& s, const Move& mv) const {
  State t = s;
  Colour us = s.turn;
  int i = mv.from, m = mv.mid, j = mv.to;
  Piece mover = piece(s.board[i]);
  uint8_t oldJ = j != i ? s.board[j] : 0;
  uint8_t oldM = m != kNone ? s.board[m] : 0;
  Role placedRole = mv.promote ? (Role)promotesTo(mover.role) : mover.role;
  t.board[i] = 0;
  t.board[j] = (uint8_t)code_[us][placedRole];
  if (m != kNone) t.board[m] = 0;
  t.flag = kNone;
  if (!isLion(mover.role)) {
    if (oldJ && isLion(roleOf(oldJ))) t.flag = (int8_t)j;
    else if (oldM && isLion(roleOf(oldM))) t.flag = (int8_t)m;
  }
  t.turn = other(us);
  return t;
}

// rules.py dead(): pawn or lance on its last rank
bool Variant::dead(Colour c, Role role, int i) const {
  return (role == P || role == L) && rankOf(i) == lastRank(c);
}

// rules.py bare_king()
bool Variant::bareKing(const uint8_t* board, Colour c) const {
  int ours = 0, royals = 0, theirs = 0, theirRoyals = 0, royalSq = kNone;
  int kc = code_[c][K];
  for (int i = 0; i < n_; ++i)
    if (board[i] == kc) royalSq = i;
  bool adjacent = false;
  for (int i = 0; i < n_; ++i) {
    if (!board[i]) continue;
    Piece p = piece(board[i]);
    if (p.colour == c) {
      if (!dead(p.colour, p.role, i)) ++ours;
      if (p.role == K) ++royals;
    } else {
      if (p.role != P && p.role != GB && !dead(p.colour, p.role, i)) {
        ++theirs;
        if (royalSq != kNone && dist(royalSq, i) == 1) adjacent = true;
      }
      if (p.role == K) ++theirRoyals;
    }
  }
  return ours == 1 && royals == 1 && theirs > 1 && theirRoyals >= 1 && !inCheck(board, other(c)) &&
         (theirs > 2 || !adjacent);
}

// rules.py status(), lishogi order
Status Variant::status(const State& s, std::vector<Move>& moves) const {
  const uint8_t* board = s.board;
  Colour us = s.turn;
  int kus = code_[us][K], kb = code_[Black][K], kw = code_[White][K];
  bool have = false;
  for (int i = 0; i < n_; ++i)
    if (board[i] == kus) have = true;
  if (!have) {
    moves.clear();
    return RoyalsLost;
  }
  if (bareKing(board, Black) || bareKing(board, White)) {
    moves.clear();
    return BareKing;
  }
  legalMoves(s, moves);
  if (moves.empty()) return Stalemate;
  int live = 0, rb = 0, rw = 0;
  for (int i = 0; i < n_; ++i) {
    if (!board[i]) continue;
    Piece p = piece(board[i]);
    if (!dead(p.colour, p.role, i)) ++live;
    if (board[i] == kb) ++rb;
    if (board[i] == kw) ++rw;
  }
  if (live == 2 && rb == 1 && rw == 1 && !inCheck(board, Black) && !inCheck(board, White)) return Draw;
  return Playing;
}

Status Variant::status(const State& s) const {
  std::vector<Move> moves;
  return status(s, moves);
}

uint64_t Variant::pack(const State& s) const {
  uint64_t v = 0, base = (uint64_t)npieces() + 1;
  for (int i = 0; i < n_; ++i) v = v * base + s.board[i];
  v = v * 2 + (s.turn == White ? 1 : 0);
  v = v * (uint64_t)(n_ + 1) + (uint64_t)(s.flag + 1);
  return v;
}

State Variant::unpack(uint64_t v) const {
  State s;
  for (int i = 0; i < kMaxSquares; ++i) s.board[i] = 0;
  uint64_t f = v % (uint64_t)(n_ + 1);
  v /= (uint64_t)(n_ + 1);
  s.flag = (int8_t)((int)f - 1);
  s.turn = (v & 1) ? White : Black;
  v >>= 1;
  uint64_t base = (uint64_t)npieces() + 1;
  for (int i = n_ - 1; i >= 0; --i) {
    s.board[i] = (uint8_t)(v % base);
    v /= base;
  }
  return s;
}

std::string Variant::show(const State& s) const {
  std::string out;
  for (int i = 0; i < n_; ++i) {
    if (!s.board[i]) continue;
    Piece p = piece(s.board[i]);
    char buf[32];
    std::snprintf(buf, sizeof buf, "%c%d:%c%s ", 'a' + fileOf(i), rankOf(i), p.colour == Black ? 'B' : 'W',
                  kRoleName[p.role]);
    out += buf;
  }
  out += s.turn == Black ? "B" : "W";
  if (s.flag != kNone) out += " flag=" + std::to_string((int)s.flag);
  return out;
}

std::string Variant::showMove(const Move& m) const {
  char buf[32];
  std::snprintf(buf, sizeof buf, "%d,%d,%d,%d", (int)m.from, (int)m.mid, (int)m.to, (int)m.promote);
  return buf;
}

}  // namespace variant
