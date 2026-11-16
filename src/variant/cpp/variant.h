// Rules engine for the small chu-like validation variants: a C++ port of
// src/variant/rules.py (which follows chushogi/src/{movegen,position,status}.cpp).
//
// A state is (board, turn, flag): board[i] is 0 (empty) or the piece code
// 1..npieces (index into the variant's piece list + 1, pieces listed Black
// first, in the variant's role order); turn is Black or White; flag is the
// counter-strike square or kNone.  Squares are indexed x * nranks + (r - 1),
// x = file from Black's left, r = rank from Black's side.  The flag is kept
// raw (not "effective only"), exactly as src/variant/bfs2.py keys states.
//
// No exceptions; fatal configuration errors abort through die().
#pragma once

#include <cstdint>
#include <string>
#include <vector>

namespace variant {

constexpr int kMaxSquares = 16;   // board packing uses one mixed-radix digit per square
constexpr int kNone = -1;

enum Colour : uint8_t { Black = 0, White = 1 };
inline Colour other(Colour c) { return c == Black ? White : Black; }

// Roles with the move tables of src/plan/moves.py.  E and O (drunk elephant,
// kirin) are only needed as "unpromoted forms" by the I10 lane check.
enum Role : uint8_t { K = 0, N, P, L, GB, B, PP, PL, PGB, PB, E, O, RoleCount };
extern const char* const kRoleName[RoleCount];
int roleByName(const std::string& name);          // -1 if unknown
int promotesTo(Role r);                           // -1 if the role does not promote
int unpromotedForm(Role r);                       // plan.lanes.UNPROMOTED; -1 if none
bool isConfinedKind(Role r);                      // P, L, GB (RC absent from the variants)
inline bool isLion(Role r) { return r == N; }

struct Dir { int8_t dx, dy; };
struct MoveTable { std::vector<Dir> steps, slides; };
const MoveTable& moveTable(Role r);

struct Piece { Colour colour; Role role; };

struct State {
  uint8_t board[kMaxSquares];
  Colour turn;
  int8_t flag;                                    // square or kNone
};

struct Move {
  int8_t from, mid, to;                           // mid = kNone for a single move
  uint8_t promote;
  bool operator==(const Move& o) const {
    return from == o.from && mid == o.mid && to == o.to && promote == o.promote;
  }
};

enum Status : uint8_t { Playing = 0, RoyalsLost, BareKing, Stalemate, Draw, StatusCount };
extern const char* const kStatusName[StatusCount];

struct StartPiece { int x, r; Colour colour; Role role; };

struct Def {
  std::string name;
  int nfiles, nranks, zone;
  std::vector<Role> roles;                        // in the Python engine's order
  std::vector<StartPiece> start;
};

// The three validation variants of src/variant/bfs.py (variants()).
const Def* findVariant(const std::string& name);
std::vector<std::string> variantNames();

[[noreturn]] void die(const std::string& msg);

class Variant {
 public:
  explicit Variant(const Def& def);

  const Def& def() const { return def_; }
  int nfiles() const { return nf_; }
  int nranks() const { return nr_; }
  int zone() const { return zone_; }
  int n() const { return n_; }                    // squares
  int npieces() const { return (int)pieces_.size(); }
  const State& start() const { return start_; }

  // geometry
  int idx(int x, int r) const { return x * nr_ + r - 1; }
  int fileOf(int i) const { return i / nr_; }
  int rankOf(int i) const { return i % nr_ + 1; }
  int dist(int i, int j) const { return dist_[i][j]; }
  bool inZone(Colour c, int r) const { return c == Black ? r > nr_ - zone_ : r <= zone_; }
  int lastRank(Colour c) const { return c == Black ? nr_ : 1; }

  // pieces
  Piece piece(uint8_t code) const { return pieces_[code - 1]; }
  int code(Colour c, Role r) const { return code_[c][r]; }   // 0 if absent from the variant
  Colour colourOf(uint8_t code) const { return pieces_[code - 1].colour; }
  Role roleOf(uint8_t code) const { return pieces_[code - 1].role; }

  // rules
  bool attacks(const uint8_t* board, int i, int j, int rem1, int rem2) const;
  bool threatened(const uint8_t* board, Colour by, int j, bool pawnsOnly, int rem1, int rem2) const;
  bool inCheck(const uint8_t* board, Colour c) const;
  bool canPromote(Role role, Colour c, int i, int j, bool capture) const;
  void legalMoves(const State& s, std::vector<Move>& out) const;   // rules.py order
  State apply(const State& s, const Move& m) const;
  bool dead(Colour c, Role role, int i) const;
  bool bareKing(const uint8_t* board, Colour c) const;
  Status status(const State& s, std::vector<Move>& moves) const;  // fills the legal moves
  Status status(const State& s) const;

  // packing: one 64-bit word per state (mixed radix npieces+1 per square, then
  // turn, then flag+1); checked to fit at construction
  uint64_t pack(const State& s) const;
  State unpack(uint64_t v) const;

  std::string show(const State& s) const;         // one-line text form for messages
  std::string showMove(const Move& m) const;

 private:
  struct Geo {
    std::vector<uint8_t> steps;                   // on-board step destinations
    std::vector<std::vector<uint8_t>> rays;       // slide rays, squares in order
  };
  struct Att { uint8_t kind; std::vector<uint8_t> path; };   // 0 none, 1 step, 2 slide

  Def def_;
  int nf_, nr_, zone_, n_;
  std::vector<Piece> pieces_;
  int code_[2][RoleCount];
  State start_;
  int dist_[kMaxSquares][kMaxSquares];
  std::vector<Geo> geo_;                          // [(colour * RoleCount + role) * n + sq]
  std::vector<Att> att_;                          // [((colour * RoleCount + role) * n + i) * n + j]
  const Geo& geo(Colour c, Role r, int i) const { return geo_[((int)c * RoleCount + r) * n_ + i]; }
  const Att& att(Colour c, Role r, int i, int j) const { return att_[(((int)c * RoleCount + r) * n_ + i) * n_ + j]; }
};

}  // namespace variant
