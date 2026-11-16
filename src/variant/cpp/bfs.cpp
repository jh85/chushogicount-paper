// Exhaustive breadth-first search of a validation variant (port of
// src/variant/bfs2.py with the same statistics).
//
//   bfs NAME [--tables FILE] [--limit N] [--depth D] [--progress N]
//
// The visited set is a bitset over (board index, side to move) for states
// without a counter-strike flag, plus one such bitset per flag class (the
// slot of the piece standing on the flag square), allocated on first use.
// The board index is Candidate::index, a dense perfect hash of a superset of
// the candidate set; a reachable state whose (rotated) board is not a
// candidate is a superset violation: it is reported and, as in bfs2.py, not
// expanded.  The queue holds packed states (Variant::pack).
//
// --limit N stops once N states have been discovered (bfs2.py semantics);
// --depth D expands no state deeper than D and prints the count per level.
// --dump-flagged FILE writes every new Black-to-move flagged state, and
// --dump-boards FILE every new Black-to-move no-flag state, as packed 64-bit
// states (Variant::pack) after a 32-byte header: "VARDUMP1", the variant name
// (8 bytes, NUL padded), the count (uint64), the kind (uint64: 1 flagged,
// 2 boards).  flagcheck reads the flagged dump.
// --queue-dir DIR keeps the queue in two files there (the level being
// expanded and the next one; same FIFO order), so that the frontier costs no
// memory; otherwise it is an in-memory std::deque (8 bytes per state).
#include <sys/resource.h>
#include <unistd.h>

#include <chrono>
#include <cstdio>
#include <cstring>
#include <deque>
#include <string>
#include <vector>

#include "candidate.h"
#include "variant.h"

using namespace variant;

namespace {

struct Bitset {
  std::vector<uint64_t> w;
  uint64_t count = 0;
  void init(uint64_t bits) { w.assign((bits + 63) / 64, 0); }
  bool testAndSet(uint64_t i) {
    uint64_t& x = w[i >> 6];
    uint64_t m = (uint64_t)1 << (i & 63);
    if (x & m) return true;
    x |= m;
    ++count;
    return false;
  }
  bool test(uint64_t i) const { return (w[i >> 6] >> (i & 63)) & 1; }
};

// FIFO of packed states: in memory, or in two files (current level / next
// level) under a directory.  Pops return states in push order either way.
class Queue {
 public:
  explicit Queue(const std::string& dir) : dir_(dir) {
    if (!dir_.empty()) {
      for (int k = 0; k < 2; ++k) {
        path_[k] = dir_ + "/bfs_queue_" + std::to_string(getpid()) + "_" + std::to_string(k) + ".bin";
        f_[k] = std::fopen(path_[k].c_str(), "w+b");
        if (!f_[k]) die("cannot create " + path_[k]);
      }
      rd_ = 0;
      wr_ = 1;
    }
  }
  ~Queue() {
    for (int k = 0; k < 2; ++k)
      if (f_[k]) {
        std::fclose(f_[k]);
        std::remove(path_[k].c_str());
      }
  }
  void push(uint64_t v) {
    ++size_;
    if (dir_.empty()) {
      dq_.push_back(v);
      return;
    }
    wbuf_.push_back(v);
    if (wbuf_.size() == kBuf) flushWrite();
  }
  uint64_t pop() {
    --size_;
    if (dir_.empty()) {
      uint64_t v = dq_.front();
      dq_.pop_front();
      return v;
    }
    if (rpos_ == rbuf_.size()) refill();
    return rbuf_[rpos_++];
  }
  uint64_t size() const { return size_; }
  bool empty() const { return size_ == 0; }
  void clear() {
    size_ = 0;
    dq_.clear();
    wbuf_.clear();
    rbuf_.clear();
    rpos_ = 0;
  }

 private:
  static constexpr size_t kBuf = 1 << 18;
  void flushWrite() {
    if (wbuf_.empty()) return;
    if (std::fwrite(wbuf_.data(), sizeof(uint64_t), wbuf_.size(), f_[wr_]) != wbuf_.size()) die("queue write failed");
    wbuf_.clear();
  }
  void refill() {
    rbuf_.resize(kBuf);
    size_t got = std::fread(rbuf_.data(), sizeof(uint64_t), kBuf, f_[rd_]);
    rpos_ = 0;
    if (got) {
      rbuf_.resize(got);
      return;
    }
    // current level exhausted: the next level's file becomes the one to read
    flushWrite();
    std::rewind(f_[rd_]);
    if (ftruncate(fileno(f_[rd_]), 0) != 0) die("queue truncate failed");
    std::swap(rd_, wr_);
    std::rewind(f_[rd_]);
    got = std::fread(rbuf_.data(), sizeof(uint64_t), kBuf, f_[rd_]);
    if (!got) die("queue underflow");
    rbuf_.resize(got);
  }
  std::string dir_, path_[2];
  FILE* f_[2] = {nullptr, nullptr};
  int rd_ = 0, wr_ = 1;
  std::deque<uint64_t> dq_;
  std::vector<uint64_t> wbuf_, rbuf_;
  size_t rpos_ = 0;
  uint64_t size_ = 0;
};

// Streamed dump of packed states with the header described above.
class DumpFile {
 public:
  void open(const std::string& path, const std::string& name, uint64_t kind) {
    f_ = std::fopen(path.c_str(), "wb");
    if (!f_) die("cannot create " + path);
    char hdr[32] = {};
    std::memcpy(hdr, "VARDUMP1", 8);
    std::strncpy(hdr + 8, name.c_str(), 8);
    std::memcpy(hdr + 24, &kind, 8);
    if (std::fwrite(hdr, 1, 32, f_) != 32) die("dump write failed");
  }
  void put(uint64_t v) {
    if (!f_) return;
    buf_.push_back(v);
    ++count_;
    if (buf_.size() == (1u << 16)) flush();
  }
  void close() {
    if (!f_) return;
    flush();
    std::fseek(f_, 16, SEEK_SET);
    if (std::fwrite(&count_, 8, 1, f_) != 1) die("dump write failed");
    std::fclose(f_);
    f_ = nullptr;
  }
  uint64_t count() const { return count_; }

 private:
  void flush() {
    if (!buf_.empty() && std::fwrite(buf_.data(), 8, buf_.size(), f_) != buf_.size()) die("dump write failed");
    buf_.clear();
  }
  FILE* f_ = nullptr;
  std::vector<uint64_t> buf_;
  uint64_t count_ = 0;
};

long peakRssKb() {
  struct rusage ru;
  getrusage(RUSAGE_SELF, &ru);
  return ru.ru_maxrss;
}

std::string dirOf(const std::string& path) {
  size_t k = path.rfind('/');
  return k == std::string::npos ? "." : path.substr(0, k);
}

}  // namespace

int main(int argc, char** argv) {
  std::string name, tablesPath, queueDir, dumpFlagged, dumpBoards;
  uint64_t limit = 0, progress = 500000;
  int depthLimit = -1;
  for (int i = 1; i < argc; ++i) {
    std::string a = argv[i];
    if (a == "--tables" && i + 1 < argc) tablesPath = argv[++i];
    else if (a == "--limit" && i + 1 < argc) limit = std::stoull(argv[++i]);
    else if (a == "--depth" && i + 1 < argc) depthLimit = std::stoi(argv[++i]);
    else if (a == "--progress" && i + 1 < argc) progress = std::stoull(argv[++i]);
    else if (a == "--queue-dir" && i + 1 < argc) queueDir = argv[++i];
    else if (a == "--dump-flagged" && i + 1 < argc) dumpFlagged = argv[++i];
    else if (a == "--dump-boards" && i + 1 < argc) dumpBoards = argv[++i];
    else if (name.empty() && a[0] != '-') name = a;
    else {
      std::fprintf(stderr, "usage: %s NAME [--tables FILE] [--limit N] [--depth D] [--progress N] [--queue-dir DIR] [--dump-flagged FILE] [--dump-boards FILE]\n", argv[0]);
      return 1;
    }
  }
  const Def* def = name.empty() ? nullptr : findVariant(name);
  if (!def) {
    std::fprintf(stderr, "unknown variant '%s'; known:", name.c_str());
    for (const std::string& s : variantNames()) std::fprintf(stderr, " %s", s.c_str());
    std::fprintf(stderr, "\n");
    return 1;
  }
  if (tablesPath.empty()) tablesPath = dirOf(argv[0]) + "/tables/" + name + ".txt";
  Variant var(*def);
  Tables tab;
  std::string err;
  if (!tab.load(tablesPath, &err)) die(err);
  Candidate cand(var, tab);
  const int n = var.n();

  auto t0 = std::chrono::steady_clock::now();
  auto secs = [&]() { return std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count(); };

  const uint64_t bits = 2 * cand.indexSize();
  std::printf("%s: |C| = %s; board index size %llu; visited bitset %.0f MB per flag class\n", name.c_str(),
              tab.total.c_str(), (unsigned long long)cand.indexSize(), bits / 8.0 / 1e6);
  std::fflush(stdout);
  Bitset noflag;
  noflag.init(bits);
  std::vector<Bitset> flagged(cand.flagClasses());

  // statistics, as in bfs2.py
  uint64_t nStates = 0;                         // discovered (incl. the start)
  uint64_t blackNonTerminal = 0, blackTerminal = 0, white = 0;
  uint64_t byStatus[StatusCount] = {};          // Black to move
  uint64_t flagNone = 0, flagEffective = 0, flagIneffective = 0;
  uint64_t violations = 0, violationsDistinctShown = 0, i10Violations = 0;
  uint64_t maxQueue = 0;
  std::vector<uint64_t> perLevel;
  uint64_t terminalStates = 0;

  Queue q(queueDir);
  DumpFile flaggedDump, boardsDump;
  if (!dumpFlagged.empty()) flaggedDump.open(dumpFlagged, name, 1);
  if (!dumpBoards.empty()) boardsDump.open(dumpBoards, name, 2);
  std::vector<Move> moves, moves2;
  uint8_t rot[kMaxSquares];

  // True if the state is new (and now marked).  Violations are not stored.
  auto visit = [&](const State& s) -> bool {
    const uint8_t* bd = s.board;
    if (s.turn == White) {
      cand.rotate(s.board, rot);
      bd = rot;
    }
    if (!cand.isCandidate(bd)) {
      ++violations;
      if (violationsDistinctShown < 5) {
        ++violationsDistinctShown;
        std::printf("  superset violation: %s\n", var.show(s).c_str());
      }
      return false;
    }
    uint64_t idx = cand.index(s.board);
    if (idx == kNoIndex) die("candidate board without an index: " + var.show(s));
    uint64_t bit = idx * 2 + (s.turn == White ? 1 : 0);
    if (s.flag == kNone) {
      bool seen = noflag.testAndSet(bit);
      if (!seen && !cand.laneOk(bd)) ++i10Violations;
      if (!seen && s.turn == Black) boardsDump.put(var.pack(s));
      return !seen;
    }
    int cls = cand.flagClass(s);
    if (cls < 0) die("flag square without an opponent piece: " + var.show(s));
    if (flagged[cls].w.empty()) {
      flagged[cls].init(bits);
      std::printf("  flag class %d (slot of the capturing piece) allocated, %.0f MB\n", cls, bits / 8.0 / 1e6);
      std::fflush(stdout);
    }
    bool seen = flagged[cls].testAndSet(bit);
    if (!seen && s.turn == Black) flaggedDump.put(var.pack(s));
    return !seen;
  };

  visit(var.start());
  q.push(var.pack(var.start()));
  nStates = 1;
  perLevel.push_back(1);
  uint64_t levelRemaining = 1, nextLevel = 0;
  int depth = 0;
  uint64_t lastReport = 0;
  bool limitHit = false;
  while (!q.empty()) {
    if (levelRemaining == 0) {
      ++depth;
      perLevel.push_back(nextLevel);
      levelRemaining = nextLevel;
      nextLevel = 0;
    }
    State st = var.unpack(q.pop());
    --levelRemaining;
    Status status = var.status(st, moves);
    if (st.turn == Black) {
      if (status != Playing) ++blackTerminal;
      else ++blackNonTerminal;
      ++byStatus[status];
      if (st.flag == kNone) {
        ++flagNone;
      } else {
        State noFlagState = st;
        noFlagState.flag = kNone;
        var.legalMoves(noFlagState, moves2);
        if (status != Playing) var.legalMoves(st, moves);   // status() may have skipped generation
        if (moves.size() != moves2.size()) ++flagEffective;
        else ++flagIneffective;
      }
    } else {
      ++white;
    }
    if (status != Playing) {
      ++terminalStates;
      continue;
    }
    if (depthLimit >= 0 && depth >= depthLimit) continue;
    for (const Move& mv : moves) {
      State nxt = var.apply(st, mv);
      if (visit(nxt)) {
        q.push(var.pack(nxt));
        ++nStates;
        ++nextLevel;
        if (limit && nStates >= limit) {
          q.clear();
          limitHit = true;
          break;
        }
      }
    }
    if (q.size() > maxQueue) maxQueue = q.size();
    if (nStates - lastReport >= progress) {
      lastReport = nStates;
      std::printf("  ... %llu states, queue %llu, depth %d, %.0fs\n", (unsigned long long)nStates,
                  (unsigned long long)q.size(), depth, secs());
      std::fflush(stdout);
    }
    if (limitHit) break;
  }

  flaggedDump.close();
  boardsDump.close();
  if (!dumpFlagged.empty())
    std::printf("  dumped %llu Black-to-move flagged states to %s\n", (unsigned long long)flaggedDump.count(), dumpFlagged.c_str());
  if (!dumpBoards.empty())
    std::printf("  dumped %llu Black-to-move boards to %s\n", (unsigned long long)boardsDump.count(), dumpBoards.c_str());
  // reachable Black-to-move boards without a flag (bfs2's |R|), and boards seen only with a flag
  uint64_t boardsB = 0, boardsOnlyFlagged = 0;
  const uint64_t evenBits = 0x5555555555555555ull;
  for (size_t i = 0; i < noflag.w.size(); ++i) {
    uint64_t base = noflag.w[i] & evenBits;
    boardsB += __builtin_popcountll(base);
    uint64_t any = 0;
    for (const Bitset& f : flagged)
      if (!f.w.empty()) any |= f.w[i];
    boardsOnlyFlagged += __builtin_popcountll(any & evenBits & ~base);
  }
  double t = secs();
  std::printf("%s: %llu reachable states in %.0fs%s\n", name.c_str(), (unsigned long long)nStates, t,
              limitHit ? "  (LIMIT HIT)" : (depthLimit >= 0 ? "  (DEPTH LIMIT)" : ""));
  std::printf("  Black to move: non-terminal %llu, terminal %llu (royalslost %llu, bareking %llu, stalemate %llu, draw %llu);"
              " White to move: %llu\n",
              (unsigned long long)blackNonTerminal, (unsigned long long)blackTerminal, (unsigned long long)byStatus[RoyalsLost],
              (unsigned long long)byStatus[BareKing], (unsigned long long)byStatus[Stalemate], (unsigned long long)byStatus[Draw],
              (unsigned long long)white);
  std::printf("  Black-to-move states by flag: none %llu, effective %llu, ineffective %llu\n", (unsigned long long)flagNone,
              (unsigned long long)flagEffective, (unsigned long long)flagIneffective);
  std::printf("  reachable Black-to-move boards |R| = %llu; |C| = %s; |R|/|C| = %.5f\n", (unsigned long long)boardsB,
              tab.total.c_str(), (double)boardsB / (double)tab.totalValue);
  std::printf("  superset violations (states that fail to rank): %llu; I10 violations: %llu\n", (unsigned long long)violations,
              (unsigned long long)i10Violations);
  std::printf("  Black-to-move boards reachable only with a flag: %llu; states popped %llu (terminal %llu); max depth %d\n",
              (unsigned long long)boardsOnlyFlagged, (unsigned long long)(blackNonTerminal + blackTerminal + white),
              (unsigned long long)terminalStates, depth);
  uint64_t flaggedStates = 0;
  for (const Bitset& f : flagged) flaggedStates += f.count;
  std::printf("  visited: no-flag %llu, flagged %llu; max queue %llu; peak RSS %.0f MB; %.0f states/s\n",
              (unsigned long long)noflag.count, (unsigned long long)flaggedStates, (unsigned long long)maxQueue,
              peakRssKb() / 1024.0, nStates / (t > 0 ? t : 1));
  if (depthLimit >= 0) {
    std::printf("  states per level:");
    for (size_t d = 0; d < perLevel.size(); ++d) std::printf(" %zu:%llu", d, (unsigned long long)perLevel[d]);
    std::printf("\n");
  }
  (void)n;
  return 0;
}
