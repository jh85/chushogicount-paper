// Port of plan/relax.py (retro-relaxation) and of plan/certify.py's checks (used inside
// relax to accept a game; callers re-certify with the engine binary).
#pragma once
#include <string>
#include <vector>

#include "core.h"
#include "eng.h"

namespace cp {

PMove parse_usi(const std::string& s);

// certify(moves, target, engine, turn): replays from the initial position; true if every
// move is legal, no terminal position before the last ply, no repeated state, and the
// final board / side to move / flag (none) / status match the target.
bool certify(const std::vector<std::string>& moves, const OBoard& target, int turn, Eng& eng,
             std::string* why = nullptr);

struct RelaxInfo {
  int tried = 0, levels = 0;
  bool ok = false;
  int retracted = 0, plies = 0, base = 0, score = 0;
};
// relax(target, eng, depth, beam, tries, planner_retries, turn); the visited set keeps a
// 128-bit digest per board (compact_seen=True).  fix_turn=false reproduces plan/relax.py up to
// 2026-10-20 exactly: its loop variable `turn` shadowed the argument, so certify() expected the
// side to move of the previous level's last frontier node, and only odd retraction depths
// could be certified.  fix_turn=true certifies against the target's own side to move.
bool relax(const OBoard& target, Eng& eng, int depth, int beam, int tries, int planner_retries, int turn,
           std::vector<std::string>& moves, RelaxInfo& info, bool fix_turn = false);

}  // namespace cp
