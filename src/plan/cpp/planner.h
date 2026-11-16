// Port of plan/planner.py (class Planner), flag-off certificates only (flag=None,
// origin=None: the only form the estimator and the follow-ups use).  Same decisions in
// the same order, so for the same target (with the same dict order), seed and options it
// plays the same game or fails with the same error.
#pragma once
#include <array>
#include <string>
#include <unordered_set>
#include <vector>

#include "core.h"
#include "eng.h"
#include "filegame.h"
#include "pycompat.h"

namespace cp {

enum class Strategy { Greedy, Peel, Edge, Deps };

struct StateKey {
  std::array<uint8_t, 146> k;
  bool operator==(const StateKey& o) const { return k == o.k; }
};
struct StateKeyHash {
  size_t operator()(const StateKey& s) const {
    uint64_t h = 1469598103934665603ULL;
    for (uint8_t b : s.k) h = (h ^ b) * 1099511628211ULL;
    return (size_t)h;
  }
};

class Planner {
 public:
  Planner(const OBoard& target, Eng& eng, int seed, int end_turn, Strategy strategy, bool defer,
          bool park);
  std::vector<std::string> run();

 private:
  // state
  OBoard target;
  int end_turn;
  Strategy strategy;
  bool defer, park;
  Eng& eng;
  std::vector<std::string> moves;
  std::unordered_set<StateKey, StateKeyHash> seen;
  std::vector<PMove> pending[2];
  std::string phase = "init";
  bool fluid_ok = false;
  SqSet reserved, protected_;
  PyRandom rng;
  Board board{};
  int turn = 0, flag = -1;
  std::vector<int> file_u[12];
  std::vector<int> doomed_lions;
  bool last_royal = false;
  int terminal_sq = -1;
  struct Deferred { int x, i; std::vector<FMove> moves; };
  std::vector<Deferred> deferred;
  int tcount[2][NROLES] = {};

  // helpers
  StateKey key(const Board& b, int t, int f) const;
  StateKey state() const { return key(board, turn, flag); }
  bool is_wall(int role) const;
  Piece bat(int s) const { if (!board[s]) key_error(s); return board[s]; }
  Piece tat(int s) const { if (!target.a[s]) key_error(s); return target.a[s]; }
  PlannerError err(const std::string& reason) const { return PlannerError{phase, reason, -1}; }
  void sync();
  bool would_repeat(const PMove& m);
  void play(int side, const PMove& m, int retry = 3);
  void do_(int side, const PMove& m, bool capture = false);
  void perturb(int side, int exclude_sq);
  void wait(int side);
  int lion_sq(int side) const;
  std::vector<int> adjacent_empty(int sq) const;
  std::vector<int> pieces(int side, int role = -1) const;
  std::vector<int> empty_squares() const;
  bool seen_after(const Board& nb, int t) const { return seen.count(key(nb, t, -1)) > 0; }

  int route(int sq, const SqSet& goals, bool capture = false, bool promote = false,
            const SqSet& walls = SqSet(), int depth = 0);
  int route_(int sq, const SqSet& goals, bool capture, bool promote, const SqSet& walls, int depth);
  void displace(int sq, const SqSet& avoid, int depth = 0, const SqSet& busy = SqSet(),
                int replans = 0, int frees = 0);
  void rescue_trapped(int frm, int to, const SqSet& segment);
  std::vector<int> frontier(int sq);
  int into_zone(int sq, int tries = 0, int cls = -1);
  void capture(int victim);

  void assign_promoted(std::vector<int> assign[2][NROLES]);
  std::vector<std::pair<int, std::pair<int, int>>> reserve_capturers();
  int target_for(int sq);
  std::vector<std::pair<int, bool>> peel_order(const SqSet& excluded);
  int instance_for(int tgt, const SqSet& inserted, const SqSet& skip = SqSet());
  void place_all_peel(const SqSet& excluded);
  void place_all_greedy(const SqSet& excluded);
  bool seals_entrance(int sq);
  bool run_deferred();
  SqSet blocked_targets() const;
  std::vector<int> entrances(int tgt, Piece piece, const SqSet& inserted);
  void place_all_edge(const SqSet& excluded);
  SqSet approach(int tgt, Piece piece, const SqSet& inserted, size_t cap = 40);
  void place_all_deps(const SqSet& excluded);
  void place_all(const SqSet& excluded);
  void terminal_capture();
  void flush();
  void fix_parity(int want);
  void verify();
};

}  // namespace cp
