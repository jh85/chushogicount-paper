// Realizable counter-strike flags of a Black-to-move board: the static
// predicate of src/plan/flags.py (realizable_flags with the predecessor
// candidate check) generalised to a variant.  A square l is accepted iff some
// White piece now on l, with its role before the move (unchanged, or the
// unpromoted form if the capture allowed promotion), could have captured a
// Black lion on l by a legal single move from an empty origin square a of a
// position P (Black lion on l, capturer on a, White to move, flag none) that
// is a candidate of the variant and, with `lanes`, satisfies I10.
#pragma once

#include <cstdint>
#include <vector>

#include "candidate.h"
#include "variant.h"

namespace variant {

struct FlagRealization {
  int8_t l, origin;
  Role prior;
  uint8_t promoted;
};

struct FlagResult {
  uint32_t accepted = 0;          // bitmask over squares, with the lane check if requested
  uint32_t acceptedNoLanes = 0;   // the same without the lane check
};

FlagResult realizableFlags(const Variant& v, const Candidate& cand, const uint8_t* board, bool lanes,
                           std::vector<FlagRealization>* out = nullptr);

// Is the flag l effective on this Black-to-move board (it removes a legal move)?
bool flagEffective(const Variant& v, const uint8_t* board, int l, std::vector<Move>& a, std::vector<Move>& b);

}  // namespace variant
