// Query tool for tests/test_variant_cpp.py: answers one line per input state.
//
//   oracle NAME [--tables FILE]
//   stdin:  c_0 c_1 ... c_{n-1} TURN FLAG      (piece codes as in rules.py, TURN B/W, FLAG square or -)
//   stdout: status NAME moves K f,m,t,p ... cand 0/1 lane 0/1 index I flagclass C packed V
//
// cand/lane are evaluated on the board rotated to Black-to-move orientation
// when TURN is W (as bfs2.py does); index is of the unrotated board.
#include <cstdio>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>

#include "candidate.h"
#include "variant.h"

using namespace variant;

int main(int argc, char** argv) {
  std::string name, tablesPath;
  for (int i = 1; i < argc; ++i) {
    std::string a = argv[i];
    if (a == "--tables" && i + 1 < argc) tablesPath = argv[++i];
    else if (name.empty()) name = a;
  }
  const Def* def = name.empty() ? nullptr : findVariant(name);
  if (!def) {
    std::fprintf(stderr, "usage: %s NAME [--tables FILE]\n", argv[0]);
    return 1;
  }
  if (tablesPath.empty()) {
    std::string a0 = argv[0];
    size_t k = a0.rfind('/');
    tablesPath = (k == std::string::npos ? std::string(".") : a0.substr(0, k)) + "/tables/" + name + ".txt";
  }
  Variant var(*def);
  Tables tab;
  std::string err;
  if (!tab.load(tablesPath, &err)) die(err);
  Candidate cand(var, tab);
  std::ios::sync_with_stdio(false);
  std::string line;
  std::vector<Move> moves;
  uint8_t rot[kMaxSquares];
  while (std::getline(std::cin, line)) {
    if (line.empty()) continue;
    std::istringstream ss(line);
    State s;
    for (int i = 0; i < kMaxSquares; ++i) s.board[i] = 0;
    for (int i = 0; i < var.n(); ++i) {
      int c;
      ss >> c;
      s.board[i] = (uint8_t)c;
    }
    std::string turn, flag;
    ss >> turn >> flag;
    s.turn = turn == "W" ? White : Black;
    s.flag = flag == "-" ? (int8_t)kNone : (int8_t)std::stoi(flag);
    Status st = var.status(s, moves);
    var.legalMoves(s, moves);
    const uint8_t* bd = s.board;
    if (s.turn == White) {
      cand.rotate(s.board, rot);
      bd = rot;
    }
    std::string out = "status " + std::string(kStatusName[st]) + " moves " + std::to_string(moves.size());
    for (const Move& m : moves) out += " " + var.showMove(m);
    out += " cand " + std::to_string((int)cand.isCandidate(bd)) + " lane " + std::to_string((int)cand.laneOk(bd));
    uint64_t idx = cand.index(s.board);
    out += " index " + (idx == kNoIndex ? std::string("-") : std::to_string(idx));
    out += " flagclass " + std::to_string(cand.flagClass(s));
    State back = var.unpack(var.pack(s));
    bool same = back.turn == s.turn && back.flag == s.flag;
    for (int i = 0; i < var.n(); ++i) same = same && back.board[i] == s.board[i];
    out += " packed " + std::to_string(var.pack(s)) + (same ? "" : " PACK-MISMATCH");
    std::cout << out << '\n';
  }
  std::cout.flush();
  return 0;
}
