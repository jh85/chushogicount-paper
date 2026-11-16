// D13 checkmate ending (docs/decisions.md) under JCSA move rules: the C++ counterpart of
// jcsa/mode.py royal_capturable() and mated().
#pragma once
#include <string>
#include <vector>

#include "../../../out/engine/src/position.h"

namespace cp {

// Can `side`'s opponent capture one of side's royals right now (no flag)?  `rules`: JCSA for
// D13; Lishogi reproduces the Python mated(Engine(), ...) of endings_share / reverify.
bool royal_capturable(const chu::Position& pos, chu::Color side, chu::RuleSet rules = chu::RuleSet::JCSA);

// The side to move has exactly one royal, it is attacked, and no legal move (JCSA move rules,
// pos.lastLionCapture as given) is an escape: a move after which the royal is not capturable,
// or (D13a) a promotion to a prince, which gives a second royal, unless the opponent can then
// capture both royals in one move (escape iff the opponent cannot capture all royals at once).  CHU_PLAN_D13_ORIGINAL=1:
// D13 as first worded (pilot P1), where the promotion is an escape only if no royal is
// capturable after it.
bool mated(const chu::Position& pos, chu::RuleSet rules = chu::RuleSet::JCSA);

// Replays `moves` from the initial position under JCSA move rules and returns the indices
// i (0..moves.size()) of the positions, before move i, in which the side to move is mated.
// *illegal is set to the first ply whose move is not JCSA-legal (the replay stops), else -1.
// MatePlanner's room-making search (plan/mateplan.py _fix) for the side to move in pos (move
// legality: pos.rules): pairs (i, j) in order, as[i] by the side to move then bs[i][j] by the
// other side, after each of which and after mv the side to move is not mated and the side
// that just moved would not be mated if it were to move (no flag); at most k pairs.
std::vector<std::pair<int, int>> fix_pairs(const chu::Position& pos, const std::string& mv,
                                           const std::vector<std::string>& as,
                                           const std::vector<std::vector<std::string>>& bs, int k);

std::vector<int> mate_plies(const std::vector<std::string>& moves, int* illegal);

}  // namespace cp
