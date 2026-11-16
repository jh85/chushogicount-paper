// Abstract file game (port of count/filegame.py) and the static candidate filter
// (count/candidates.py is_candidate at level "file", colour classes, PRIMARY setup).
#pragma once
#include <map>
#include <set>
#include <string>
#include <vector>

#include "core.h"

namespace cp {

struct Slot {
  std::string name;
  int colour;   // 0 B, 1 W
  int kind;     // P, L, RC, GB
  int start;
  std::string repr() const;
};
const std::vector<Slot>& chu_file_slots(int x);

constexpr int CAPTURED = 0, PROMOTED = -1;
using FState = std::vector<int>;
struct FMove {      // (i, a, b) or (i, a, b, PROMOTED)
  int i, a, b;
  bool prom;
  bool operator==(const FMove& o) const { return i == o.i && a == o.a && b == o.b && prom == o.prom; }
};
// shortest strict play to `target`, captures first; false if unreachable
bool path_to(int x, const FState& target, std::vector<FMove>& out);
std::string rstate(const FState& s);

// file_features(chu_setup(...), x, u, "file", True): nullptr if u is not admissible
struct FileFeat {
  int cb, cw, j;
  std::vector<std::pair<std::pair<int, int>, int>> elig;   // ((colour, kind), 0/1), slot order, kind != P
};
bool file_features(int x, const std::vector<int>& u, FileFeat& out);

// is_candidate(chu_setup("file", mover_royal_required=False, identify_royals=True), board, "file", True)
bool is_candidate_primary(const Board& board);

}  // namespace cp
