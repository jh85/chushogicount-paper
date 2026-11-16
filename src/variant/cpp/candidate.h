// Candidate test (port of count.candidates.is_candidate on the exported
// per-file tables), the I10 lane check (plan.lanes.lane_ok), the 180-degree
// colour swap, and a dense "superset index" of boards used as the bitset
// index of the search.
#pragma once

#include <cstdint>
#include <string>
#include <unordered_map>
#include <vector>

#include "variant.h"

namespace variant {

constexpr uint64_t kNoIndex = ~(uint64_t)0;

// Data of src/variant/export_tables.py for one variant.
struct Tables {
  std::string name;
  int nfiles = 0, nranks = 0, zone = 0;
  bool colour = false;
  std::string total;                              // exact |C_V| as a decimal string
  uint64_t totalValue = 0;
  struct Etype { Colour colour; Role kind; };
  std::vector<Etype> etypes;
  struct Group {
    Colour colour;
    Role role;
    int max, minimum;
    bool promotable, bound;
    std::vector<int> classes;                     // Bound: start colour classes
  };
  std::vector<Group> groups;
  struct Slot { std::string name; Colour colour; Role kind; int start; };
  std::vector<std::vector<Slot>> files;
  struct Cfg { int cb, cw, j; std::vector<int> elig; };
  std::vector<std::unordered_map<uint32_t, Cfg>> cfgs;   // per file, key = ranks in mixed radix nranks+1

  bool load(const std::string& path, std::string* err);
};

class Candidate {
 public:
  Candidate(const Variant& v, const Tables& t);

  const Tables& tables() const { return t_; }
  // Black-to-move orientation, as count.candidates.is_candidate(setup, board, "file", colour)
  bool isCandidate(const uint8_t* board) const;
  // plan.lanes.lane_ok with the Geometry of the setup
  bool laneOk(const uint8_t* board) const;
  // 180-degree rotation with colour swap (bfs2.rotate); flag rotated too
  void rotate(const uint8_t* in, uint8_t* out) const;
  int rotateSquare(int i) const { return v_.n() - 1 - i; }

  // Dense index of every board whose unpromoted confined pieces stand on their
  // own file (a superset of C_V); kNoIndex otherwise.
  uint64_t index(const uint8_t* board) const;
  uint64_t indexSize() const { return size_; }
  // inverse of index(): the board (n squares, rest zero) with that index; false if idx >= indexSize()
  bool unindex(uint64_t idx, uint8_t* board) const;
  // slot (0..flagClasses()-1) of the piece with this code
  int slotClass(uint8_t code) const { return slotOfCode_[code] % nslotsPerColour_; }
  // flag class: index of the slot (K, free piece, pawn, lance/go-between) of the
  // piece on the flag square, which belongs to the side not to move; -1 if
  // the square is empty or holds a piece of the side to move.
  int flagClass(const State& s) const;
  int flagClasses() const { return nslotsPerColour_; }
  // first square holding the piece of slot `cls` of colour c, or kNone
  int squareOfSlot(const uint8_t* board, Colour c, int cls) const;

 private:
  const Variant& v_;
  const Tables& t_;
  // lane geometry
  std::vector<uint32_t> laneMasks_[2][RoleCount];          // [colour][form][sq] -> list of S masks (flattened)
  std::vector<int> laneOff_[2][RoleCount];                  // offsets into laneMasks_ per square
  int wallStart_[2][RoleCount][kMaxSquares];                // start rank per (colour, kind, file), 0 if none
  // superset index
  struct Slot { Colour colour; Role role; int promoted; bool confined; int file; int cs, fs; };
  std::vector<Slot> slots_;                                 // per (colour, unpromoted role)
  int slotOfCode_[64];
  int nslotsPerColour_ = 0;
  int ncs_ = 0;                                             // confined slots
  std::vector<int> csSlot_;                                 // cs -> slot
  std::vector<int> fsSlot_;                                 // fs -> slot (free entries incl. promoted confined)
  std::vector<int> fsRadix_;                                // variants + 1
  std::vector<int> fsVariantOfCode_;                        // code -> variant number (1..) within its fs entry, 0 if confined-unpromoted
  std::vector<int> fsOfCode_;                               // code -> fs entry or -1
  std::vector<uint64_t> ucfgBase_;                          // mixed-radix u-config id -> base offset or kNoIndex
  std::vector<uint32_t> ucfgMask_;
  std::vector<std::vector<uint64_t>> offs_;                 // [mask][pidx] -> offset within the u-config block
  std::vector<uint64_t> maskSize_;
  std::vector<uint64_t> validBase_;                         // bases of the valid u-configs, increasing
  std::vector<uint32_t> validId_;
  std::vector<std::vector<uint8_t>> fsCode_;                // [fs][variant] -> piece code (variant 0 unused)
  uint64_t size_ = 0;
  int known_[2][RoleCount];                                 // role belongs to a free group of that colour
};

}  // namespace variant
