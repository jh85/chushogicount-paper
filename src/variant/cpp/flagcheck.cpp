// Flag-state check of a validation variant (docs/variant-cpp.md, "Flag states").
//
//   flagcheck NAME full --flagged DUMP [--threads T] [--no-lanes] [--tables FILE]
//       (a) every reachable Black-to-move flagged state of the dump (written by
//           `bfs NAME --dump-flagged DUMP`) must be accepted by the realizable-
//           flags predicate; counterexamples (up to 20) are printed;
//       (b) over every candidate board of the variant (enumerated through the
//           dense board index), the accepted flag states are counted and split
//           into reachable / unreachable with the dump's flag bitsets.
//   flagcheck NAME xval [--no-lanes] [--tables FILE]
//       stdin: one board per line (n piece codes, Black to move);
//       stdout: "accepted l1 l2 ... ; nolanes l1 l2 ..." (sorted squares).
#include <atomic>
#include <cstdio>
#include <cstring>
#include <iostream>
#include <mutex>
#include <sstream>
#include <string>
#include <thread>
#include <vector>

#include "candidate.h"
#include "flags.h"
#include "variant.h"

using namespace variant;

namespace {

struct Dump {
  std::string name;
  uint64_t kind = 0;
  std::vector<uint64_t> states;
};

bool readDump(const std::string& path, Dump* d, std::string* err) {
  FILE* f = std::fopen(path.c_str(), "rb");
  if (!f) {
    *err = "cannot open " + path;
    return false;
  }
  char magic[8], name[8];
  uint64_t count;
  if (std::fread(magic, 1, 8, f) != 8 || std::memcmp(magic, "VARDUMP1", 8) != 0 || std::fread(name, 1, 8, f) != 8 ||
      std::fread(&count, 8, 1, f) != 1 || std::fread(&d->kind, 8, 1, f) != 1) {
    *err = path + ": bad header";
    std::fclose(f);
    return false;
  }
  d->name = std::string(name, strnlen(name, 8));
  d->states.resize(count);
  if (count && std::fread(d->states.data(), 8, count, f) != count) {
    *err = path + ": truncated";
    std::fclose(f);
    return false;
  }
  std::fclose(f);
  return true;
}

struct Bits {
  std::vector<uint64_t> w;
  void init(uint64_t bits) { w.assign((bits + 63) / 64, 0); }
  void set(uint64_t i) { w[i >> 6] |= (uint64_t)1 << (i & 63); }
  bool test(uint64_t i) const { return !w.empty() && ((w[i >> 6] >> (i & 63)) & 1); }
};

struct Counts {
  uint64_t indices = 0, candidates = 0, candNoKing = 0, boardsWithFlags = 0;
  uint64_t accepted = 0, acceptedReachable = 0, acceptedUnreachable = 0;
  uint64_t acceptedNoLanes = 0, acceptedEffective = 0, acceptedEffectiveReachable = 0;
  void add(const Counts& o) {
    indices += o.indices;
    candidates += o.candidates;
    candNoKing += o.candNoKing;
    boardsWithFlags += o.boardsWithFlags;
    accepted += o.accepted;
    acceptedReachable += o.acceptedReachable;
    acceptedUnreachable += o.acceptedUnreachable;
    acceptedNoLanes += o.acceptedNoLanes;
    acceptedEffective += o.acceptedEffective;
    acceptedEffectiveReachable += o.acceptedEffectiveReachable;
  }
};

}  // namespace

int main(int argc, char** argv) {
  std::string name, mode, tablesPath, dumpPath;
  int threads = 1;
  bool lanes = true;
  for (int i = 1; i < argc; ++i) {
    std::string a = argv[i];
    if (a == "--tables" && i + 1 < argc) tablesPath = argv[++i];
    else if (a == "--flagged" && i + 1 < argc) dumpPath = argv[++i];
    else if (a == "--threads" && i + 1 < argc) threads = std::stoi(argv[++i]);
    else if (a == "--no-lanes") lanes = false;
    else if (name.empty() && a[0] != '-') name = a;
    else if (mode.empty() && a[0] != '-') mode = a;
    else {
      std::fprintf(stderr, "usage: %s NAME full --flagged DUMP [--threads T] [--no-lanes] | NAME xval\n", argv[0]);
      return 1;
    }
  }
  const Def* def = name.empty() ? nullptr : findVariant(name);
  if (!def || (mode != "full" && mode != "xval")) {
    std::fprintf(stderr, "usage: %s NAME full --flagged DUMP [--threads T] [--no-lanes] | NAME xval\n", argv[0]);
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
  const int n = var.n();

  if (mode == "xval") {
    std::ios::sync_with_stdio(false);
    std::string line;
    while (std::getline(std::cin, line)) {
      if (line.empty()) continue;
      std::istringstream ss(line);
      uint8_t board[kMaxSquares] = {};
      for (int i = 0; i < n; ++i) {
        int c;
        ss >> c;
        board[i] = (uint8_t)c;
      }
      FlagResult r = realizableFlags(var, cand, board, lanes);
      std::string out = "accepted";
      for (int l = 0; l < n; ++l)
        if (r.accepted & (1u << l)) out += " " + std::to_string(l);
      out += " ; nolanes";
      for (int l = 0; l < n; ++l)
        if (r.acceptedNoLanes & (1u << l)) out += " " + std::to_string(l);
      std::cout << out << '\n';
    }
    return 0;
  }

  // ---- full: (a) the reachable flagged states ------------------------------
  Dump dump;
  if (dumpPath.empty() || !readDump(dumpPath, &dump, &err)) die(dumpPath.empty() ? "--flagged DUMP required" : err);
  if (dump.name != name || dump.kind != 1) die("dump is not a flagged-state dump of " + name);
  std::printf("%s: %zu reachable Black-to-move flagged states in %s; lane check %s\n", name.c_str(), dump.states.size(),
              dumpPath.c_str(), lanes ? "on" : "off");
  const uint64_t bits = 2 * cand.indexSize();
  std::vector<Bits> reach(cand.flagClasses());
  uint64_t accepted = 0, rejected = 0, acceptedNoLanes = 0, effective = 0, shown = 0;
  {
    std::vector<Move> ma, mb;
    for (uint64_t packed : dump.states) {
      State s = var.unpack(packed);
      if (s.turn != Black || s.flag == kNone) die("dump entry is not a Black-to-move flagged state");
      uint64_t idx = cand.index(s.board);
      int cls = cand.flagClass(s);
      if (idx == kNoIndex || cls < 0) die("dump entry without index or flag class: " + var.show(s));
      if (reach[cls].w.empty()) reach[cls].init(bits);
      reach[cls].set(idx * 2);
      FlagResult r = realizableFlags(var, cand, s.board, lanes);
      if (r.acceptedNoLanes & (1u << s.flag)) ++acceptedNoLanes;
      if (flagEffective(var, s.board, s.flag, ma, mb)) ++effective;
      if (r.accepted & (1u << s.flag)) {
        ++accepted;
      } else {
        ++rejected;
        if (shown < 20) {
          ++shown;
          std::printf("  NOT ACCEPTED: %s\n", var.show(s).c_str());
        }
      }
    }
  }
  std::printf("  (a) reachable flagged states: accepted %llu, not accepted %llu (without the lane check: accepted %llu);"
              " effective %llu\n",
              (unsigned long long)accepted, (unsigned long long)rejected, (unsigned long long)acceptedNoLanes,
              (unsigned long long)effective);
  std::fflush(stdout);

  // ---- (b) every candidate board ---------------------------------------------
  const uint64_t size = cand.indexSize();
  const uint64_t chunk = 1 << 16;
  std::atomic<uint64_t> next(0);
  std::mutex mu;
  Counts total;
  std::vector<std::thread> pool;
  for (int t = 0; t < threads; ++t)
    pool.emplace_back([&]() {
      Counts c;
      uint8_t board[kMaxSquares];
      std::vector<Move> ma, mb;
      const int bk = var.code(Black, K);
      for (;;) {
        uint64_t lo = next.fetch_add(chunk);
        if (lo >= size) break;
        uint64_t hi = std::min(size, lo + chunk);
        for (uint64_t idx = lo; idx < hi; ++idx) {
          cand.unindex(idx, board);
          ++c.indices;
          if (!cand.isCandidate(board)) continue;
          ++c.candidates;
          bool king = false;
          for (int i = 0; i < n; ++i)
            if (board[i] == bk) king = true;
          if (!king) {
            ++c.candNoKing;
            continue;
          }
          FlagResult r = realizableFlags(var, cand, board, lanes);
          if (r.accepted) ++c.boardsWithFlags;
          for (int l = 0; l < n; ++l) {
            if (r.acceptedNoLanes & (1u << l)) ++c.acceptedNoLanes;
            if (!(r.accepted & (1u << l))) continue;
            ++c.accepted;
            bool reachable = reach[cand.slotClass(board[l])].test(idx * 2);
            if (reachable) ++c.acceptedReachable;
            else ++c.acceptedUnreachable;
            if (flagEffective(var, board, l, ma, mb)) {
              ++c.acceptedEffective;
              if (reachable) ++c.acceptedEffectiveReachable;
            }
          }
        }
      }
      std::lock_guard<std::mutex> g(mu);
      total.add(c);
    });
  for (std::thread& th : pool) th.join();
  std::printf("  (b) board index %llu entries, candidates %llu (|C| = %s%s), of which without a Black king %llu\n",
              (unsigned long long)total.indices, (unsigned long long)total.candidates, tab.total.c_str(),
              total.candidates == tab.totalValue ? ", equal" : ", MISMATCH", (unsigned long long)total.candNoKing);
  std::printf("  accepted flag states over all candidates: %llu on %llu boards (without the lane check %llu);"
              " accepted and reachable %llu, accepted and unreachable %llu, reachable and not accepted %llu\n",
              (unsigned long long)total.accepted, (unsigned long long)total.boardsWithFlags,
              (unsigned long long)total.acceptedNoLanes, (unsigned long long)total.acceptedReachable,
              (unsigned long long)total.acceptedUnreachable, (unsigned long long)rejected);
  std::printf("  accepted and effective: %llu, of which reachable %llu; share of accepted flag states that are reachable:"
              " %.5f\n",
              (unsigned long long)total.acceptedEffective, (unsigned long long)total.acceptedEffectiveReachable,
              total.accepted ? (double)total.acceptedReachable / (double)total.accepted : 0.0);
  if (total.acceptedReachable != accepted)
    std::printf("  WARNING: accepted-and-reachable (%llu) differs from the accepted dump states (%llu)\n",
                (unsigned long long)total.acceptedReachable, (unsigned long long)accepted);
  std::printf("%s\n", rejected == 0 && total.candidates == tab.totalValue && total.acceptedReachable == accepted ? "OK" : "FAIL");
  return rejected == 0 ? 0 : 1;
}
