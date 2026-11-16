// In-process adapter to the reference engine (chushogi/src, compiled unchanged): the same
// commands plan/engine.py sends over the pipe (position, legal, move, sfen, status), with
// boards converted directly instead of through SFEN text (same mapping as count/sfen.py
// and count/sampler.py to_sfen).
#pragma once
#include <vector>

#include "core.h"
#include "../../../out/engine/src/movegen.h"
#include "../../../out/engine/src/position.h"
#include "../../../out/engine/src/status.h"

namespace cp {

class Eng {
 public:
  void set_initial();
  // position from a planner board (to_sfen: N, Q, K written as lion, free king, king), flag "-"
  void set_board(const Board& b, int turn, int flag = -1);   // flag: planner square or -1
  const std::vector<chu::Move>& legal();
  bool is_legal(const PMove& m);
  void move(const PMove& m);                // asserts legality, as plan/engine.py
  bool playing();                           // status == "playing"
  // parse(sfen()): planner board, side to move, flag square (-1 for none)
  void state(Board& b, int& turn, int& flag) const;
  const chu::Position& pos() const { return pos_; }

 private:
  chu::Position pos_;
  std::vector<chu::Move> legal_;
  bool valid_ = false;
};

int to_esq(int s);     // planner square -> engine square
Piece from_epiece(uint8_t p);   // engine piece (non-zero) -> planner piece
int from_esq(int e);   // engine square -> planner square

}  // namespace cp
