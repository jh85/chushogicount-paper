// See candidate.h.
#include "candidate.h"

#include <algorithm>
#include <fstream>
#include <sstream>

namespace variant {

namespace {

Colour colourByName(const std::string& s, bool* ok) {
  *ok = s == "B" || s == "W";
  return s == "W" ? White : Black;
}

Role roleOrDie(const std::string& s) {
  int r = roleByName(s);
  if (r < 0) die("unknown role in tables: " + s);
  return (Role)r;
}

uint64_t falling(int n, int k) {
  uint64_t r = 1;
  for (int i = 0; i < k; ++i) r *= (uint64_t)(n - i);
  return r;
}

}  // namespace

bool Tables::load(const std::string& path, std::string* err) {
  std::ifstream in(path);
  if (!in) {
    *err = "cannot open " + path;
    return false;
  }
  std::string line;
  int lineNo = 0;
  while (std::getline(in, line)) {
    ++lineNo;
    if (line.empty() || line[0] == '#') continue;
    std::istringstream ss(line);
    std::string tag;
    ss >> tag;
    bool ok = true;
    if (tag == "variant") {
      int c;
      ss >> name >> nfiles >> nranks >> zone >> c;
      colour = c != 0;
      files.assign(nfiles, {});
      cfgs.assign(nfiles, {});
    } else if (tag == "total") {
      ss >> total;
      totalValue = 0;
      for (char ch : total) totalValue = totalValue * 10 + (uint64_t)(ch - '0');
    } else if (tag == "etypes") {
      int k;
      ss >> k;
      for (int i = 0; i < k; ++i) {
        std::string c, r;
        ss >> c >> r;
        etypes.push_back(Etype{colourByName(c, &ok), roleOrDie(r)});
      }
    } else if (tag == "group") {
      std::string c, r, extra;
      Group g;
      int promotable;
      ss >> c >> r >> g.max >> promotable >> g.minimum;
      g.colour = colourByName(c, &ok);
      g.role = roleOrDie(r);
      g.promotable = promotable != 0;
      g.bound = false;
      if (ss >> extra) {
        if (extra != "bound") ok = false;
        g.bound = true;
        int cls;
        while (ss >> cls) g.classes.push_back(cls);
      }
      ss.clear();                                 // end of line is not an error
      groups.push_back(g);
    } else if (tag == "file") {
      int x, k;
      ss >> x >> k;
      if (x < 0 || x >= nfiles) ok = false;
      for (int i = 0; ok && i < k; ++i) {
        Slot s;
        std::string c, r;
        ss >> s.name >> c >> r >> s.start;
        s.colour = colourByName(c, &ok);
        s.kind = roleOrDie(r);
        files[x].push_back(s);
      }
    } else if (tag == "cfg") {
      int x;
      ss >> x;
      if (x < 0 || x >= nfiles) {
        ok = false;
      } else {
        uint32_t key = 0;
        for (size_t i = 0; i < files[x].size(); ++i) {
          int r;
          ss >> r;
          key = key * (uint32_t)(nranks + 1) + (uint32_t)r;
        }
        Cfg cfg;
        ss >> cfg.cb >> cfg.cw >> cfg.j;
        for (size_t i = 0; i < etypes.size(); ++i) {
          int e;
          ss >> e;
          cfg.elig.push_back(e);
        }
        cfgs[x][key] = cfg;
      }
    } else {
      ok = false;
    }
    if (!ok || ss.fail()) {
      *err = path + ":" + std::to_string(lineNo) + ": cannot parse";
      return false;
    }
  }
  if (name.empty() || total.empty()) {
    *err = path + ": incomplete";
    return false;
  }
  return true;
}

Candidate::Candidate(const Variant& v, const Tables& t) : v_(v), t_(t) {
  if (t.nfiles != v.nfiles() || t.nranks != v.nranks() || t.zone != v.zone() || t.name != v.def().name)
    die("tables do not match the variant");
  const int n = v.n();
  // known roles (free groups) and wall start ranks
  for (int c = 0; c < 2; ++c)
    for (int r = 0; r < RoleCount; ++r) {
      known_[c][r] = 0;
      for (int x = 0; x < kMaxSquares; ++x) wallStart_[c][r][x] = 0;
    }
  for (const Tables::Group& g : t.groups) {
    known_[g.colour][g.role] = 1;
    int p = promotesTo(g.role);
    if ((g.promotable || g.bound) && p >= 0) known_[g.colour][p] = 1;
  }
  for (int x = 0; x < t.nfiles; ++x)
    for (const Tables::Slot& s : t.files[x]) wallStart_[s.colour][s.kind][x] = s.start;
  // plan.lanes.START_RANK fallback (chu shogi) for walls without a slot
  const int chuStart[2][2] = {{4, 1}, {9, 12}};   // [colour][P, L]
  for (int c = 0; c < 2; ++c)
    for (int x = 0; x < t.nfiles; ++x) {
      if (!wallStart_[c][P][x]) wallStart_[c][P][x] = chuStart[c][0];
      if (!wallStart_[c][L][x]) wallStart_[c][L][x] = chuStart[c][1];
    }
  // lane masks: plan.lanes.entrances_with_paths on an otherwise empty board
  for (int c = 0; c < 2; ++c) {
    int sign = c == Black ? 1 : -1;
    for (int r = 0; r < RoleCount; ++r) {
      std::vector<uint32_t>& masks = laneMasks_[c][r];
      std::vector<int>& off = laneOff_[c][r];
      off.assign(n + 1, 0);
      const MoveTable& mt = moveTable((Role)r);
      for (int sq = 0; sq < n; ++sq) {
        off[sq] = (int)masks.size();
        int x = v.fileOf(sq), rk = v.rankOf(sq);
        for (const Dir& d : mt.steps) {
          int ex = x - d.dx, er = rk - d.dy * sign;
          if (ex >= 0 && ex < v.nfiles() && er >= 1 && er <= v.nranks())
            masks.push_back((1u << sq) | (1u << v.idx(ex, er)));
        }
        for (const Dir& d : mt.slides) {
          uint32_t path = 0;
          int ex = x - d.dx, er = rk - d.dy * sign;
          while (ex >= 0 && ex < v.nfiles() && er >= 1 && er <= v.nranks()) {
            int e = v.idx(ex, er);
            masks.push_back((1u << sq) | (1u << e) | path);
            path |= 1u << e;
            ex -= d.dx;
            er -= d.dy * sign;
          }
        }
      }
      off[n] = (int)masks.size();
    }
  }
  // slots: one per (colour, unpromoted role); every (colour, role) occurs at most once
  for (int i = 0; i < 64; ++i) slotOfCode_[i] = -1;
  fsOfCode_.assign(v.npieces() + 1, -1);
  fsVariantOfCode_.assign(v.npieces() + 1, 0);
  for (int c = 0; c < 2; ++c) {
    int count = 0;
    for (Role r : v.def().roles) {
      if (kRoleName[r][0] == '+') continue;
      Slot s;
      s.colour = (Colour)c;
      s.role = r;
      s.promoted = promotesTo(r) >= 0 && v.code((Colour)c, (Role)promotesTo(r)) ? promotesTo(r) : -1;
      s.confined = isConfinedKind(r);
      s.file = -1;
      s.cs = s.fs = -1;
      if (s.confined) {
        for (int x = 0; x < t.nfiles; ++x)
          for (const Tables::Slot& fs : t.files[x])
            if (fs.colour == s.colour && fs.kind == s.role) s.file = x;
        if (s.file < 0) die("confined piece without a file slot: " + std::string(kRoleName[r]));
      }
      slotOfCode_[v.code((Colour)c, r)] = (int)slots_.size();
      if (s.promoted >= 0) slotOfCode_[v.code((Colour)c, (Role)s.promoted)] = (int)slots_.size();
      slots_.push_back(s);
      ++count;
    }
    if (c == 0) nslotsPerColour_ = count;
    else if (count != nslotsPerColour_) die("asymmetric slots");
  }
  for (const Tables::Group& g : t.groups)
    if (g.max != 1) die("superset index assumes one piece per (colour, role)");
  for (int i = 0; i < (int)slots_.size(); ++i)
    if (slots_[i].confined) {
      slots_[i].cs = ncs_;
      csSlot_.push_back(i);
      ++ncs_;
    }
  // free entries: non-confined slots first, then the promoted forms of the confined ones
  for (int i = 0; i < (int)slots_.size(); ++i) {
    Slot& s = slots_[i];
    if (s.confined) continue;
    s.fs = (int)fsSlot_.size();
    fsSlot_.push_back(i);
    fsRadix_.push_back(s.promoted >= 0 ? 3 : 2);
    fsOfCode_[v.code(s.colour, s.role)] = s.fs;
    fsVariantOfCode_[v.code(s.colour, s.role)] = 1;
    if (s.promoted >= 0) {
      fsOfCode_[v.code(s.colour, (Role)s.promoted)] = s.fs;
      fsVariantOfCode_[v.code(s.colour, (Role)s.promoted)] = 2;
    }
  }
  for (int i = 0; i < (int)slots_.size(); ++i) {
    Slot& s = slots_[i];
    if (!s.confined || s.promoted < 0) continue;
    s.fs = (int)fsSlot_.size();
    fsSlot_.push_back(i);
    fsRadix_.push_back(2);
    fsOfCode_[v.code(s.colour, (Role)s.promoted)] = s.fs;
    fsVariantOfCode_[v.code(s.colour, (Role)s.promoted)] = 1;
  }
  const int nfs = (int)fsSlot_.size();
  uint64_t R = 1;
  for (int r : fsRadix_) R *= (uint64_t)r;
  // offsets per (mask of confined slots that are not on the board unpromoted, p-vector)
  offs_.assign(1u << ncs_, {});
  maskSize_.assign(1u << ncs_, 0);
  for (uint32_t mask = 0; mask < (1u << ncs_); ++mask) {
    int d = ncs_ - __builtin_popcount(mask);
    int nsq = n - d;
    std::vector<uint64_t>& o = offs_[mask];
    o.assign(R + 1, 0);
    uint64_t run = 0;
    for (uint64_t pidx = 0; pidx < R; ++pidx) {
      uint64_t vv = pidx;
      int m = 0;
      bool valid = true;
      for (int f = nfs - 1; f >= 0; --f) {
        int digit = (int)(vv % (uint64_t)fsRadix_[f]);
        vv /= (uint64_t)fsRadix_[f];
        if (!digit) continue;
        ++m;
        const Slot& s = slots_[fsSlot_[f]];
        if (s.confined && !(mask & (1u << s.cs))) valid = false;
      }
      o[pidx] = run;
      if (valid) run += falling(nsq, m);
    }
    o[R] = run;
    maskSize_[mask] = run;
  }
  // u-configs
  uint64_t U = 1;
  for (int i = 0; i < ncs_; ++i) U *= (uint64_t)(v.nranks() + 1);
  ucfgBase_.assign(U, kNoIndex);
  ucfgMask_.assign(U, 0);
  for (uint64_t id = 0; id < U; ++id) {
    uint64_t vv = id;
    std::vector<int> u(ncs_);
    for (int k = ncs_ - 1; k >= 0; --k) {
      u[k] = (int)(vv % (uint64_t)(v.nranks() + 1));
      vv /= (uint64_t)(v.nranks() + 1);
    }
    bool valid = true;
    uint32_t mask = 0;
    for (int a = 0; a < ncs_; ++a) {
      if (!u[a]) {
        mask |= 1u << a;
        continue;
      }
      for (int b = a + 1; b < ncs_; ++b)
        if (u[b] == u[a] && slots_[csSlot_[a]].file == slots_[csSlot_[b]].file) valid = false;
    }
    if (!valid) continue;
    ucfgBase_[id] = size_;
    ucfgMask_[id] = mask;
    validBase_.push_back(size_);
    validId_.push_back((uint32_t)id);
    size_ += maskSize_[mask];
  }
  fsCode_.assign(nfs, std::vector<uint8_t>(3, 0));
  for (int c = 1; c <= v.npieces(); ++c)
    if (fsOfCode_[c] >= 0) fsCode_[fsOfCode_[c]][fsVariantOfCode_[c]] = (uint8_t)c;
}

bool Candidate::unindex(uint64_t idx, uint8_t* board) const {
  const int n = v_.n();
  if (idx >= size_) return false;
  for (int i = 0; i < kMaxSquares; ++i) board[i] = 0;
  size_t k = (size_t)(std::upper_bound(validBase_.begin(), validBase_.end(), idx) - validBase_.begin()) - 1;
  uint64_t id = validId_[k], off = idx - validBase_[k];
  uint32_t mask = ucfgMask_[id];
  uint32_t confined = 0;
  for (int c = ncs_ - 1; c >= 0; --c) {
    int r = (int)(id % (uint64_t)(v_.nranks() + 1));
    id /= (uint64_t)(v_.nranks() + 1);
    if (!r) continue;
    const Slot& s = slots_[csSlot_[c]];
    int sq = v_.idx(s.file, r);
    board[sq] = (uint8_t)v_.code(s.colour, s.role);
    confined |= 1u << sq;
  }
  const std::vector<uint64_t>& o = offs_[mask];
  size_t pidx = (size_t)(std::upper_bound(o.begin(), o.end(), off) - o.begin()) - 1;
  uint64_t rank = off - o[pidx];
  const int nfs = (int)fsSlot_.size();
  int p[16];
  uint64_t vv = pidx;
  int m = 0;
  for (int f = nfs - 1; f >= 0; --f) {
    p[f] = (int)(vv % (uint64_t)fsRadix_[f]);
    vv /= (uint64_t)fsRadix_[f];
    if (p[f]) ++m;
  }
  uint8_t remaining[kMaxSquares];
  int nrem = 0;
  for (int i = 0; i < n; ++i)
    if (!(confined & (1u << i))) remaining[nrem++] = (uint8_t)i;
  int t = 0;
  for (int f = 0; f < nfs; ++f) {
    if (!p[f]) continue;
    uint64_t divisor = falling(nrem - 1, m - t - 1);
    int pos = (int)(rank / divisor);
    rank %= divisor;
    board[remaining[pos]] = fsCode_[f][p[f]];
    for (int q = pos; q + 1 < nrem; ++q) remaining[q] = remaining[q + 1];
    --nrem;
    ++t;
  }
  return true;
}

void Candidate::rotate(const uint8_t* in, uint8_t* out) const {
  const int n = v_.n();
  for (int i = 0; i < n; ++i) {
    uint8_t c = in[i];
    out[n - 1 - i] = c ? (uint8_t)v_.code(other(v_.colourOf(c)), v_.roleOf(c)) : 0;
  }
  for (int i = n; i < kMaxSquares; ++i) out[i] = 0;
}

// count.candidates.is_candidate(setup, board, "file", colour)
bool Candidate::isCandidate(const uint8_t* board) const {
  const int n = v_.n();
  int cnt[2][RoleCount] = {};
  int onClass[2][RoleCount][2] = {};
  for (int i = 0; i < n; ++i)
    if (board[i]) {
      Piece p = v_.piece(board[i]);
      ++cnt[p.colour][p.role];
      ++onClass[p.colour][p.role][(v_.fileOf(i) + v_.rankOf(i)) % 2];
    }
  int cb = 0, cw = 0, jj = 0;
  std::vector<int> caps(t_.etypes.size(), 0);
  bool anyPawnSlot = false;
  for (int x = 0; x < t_.nfiles; ++x) {
    const std::vector<Tables::Slot>& slots = t_.files[x];
    int u[8] = {};
    for (const Tables::Slot& s : slots)
      if (s.kind == P) anyPawnSlot = true;
    for (int r = 1; r <= t_.nranks; ++r) {
      uint8_t c = board[v_.idx(x, r)];
      if (!c) continue;
      Piece p = v_.piece(c);
      if (!isConfinedKind(p.role) || known_[p.colour][p.role]) continue;
      int i = -1;
      for (size_t k = 0; k < slots.size(); ++k)
        if (slots[k].colour == p.colour && slots[k].kind == p.role) i = (int)k;
      if (i < 0 || u[i]) return false;                     // I1
      u[i] = r;
    }
    uint32_t key = 0;
    for (size_t k = 0; k < slots.size(); ++k) key = key * (uint32_t)(t_.nranks + 1) + (uint32_t)u[k];
    auto it = t_.cfgs[x].find(key);
    if (it == t_.cfgs[x].end()) return false;              // I2, I3 (file game)
    cb += it->second.cb;
    cw += it->second.cw;
    jj += it->second.j;
    for (size_t k = 0; k < caps.size(); ++k) caps[k] += it->second.elig[k];
  }
  for (size_t k = 0; k < caps.size(); ++k) {
    int pr = promotesTo(t_.etypes[k].kind);
    int have = pr >= 0 ? cnt[t_.etypes[k].colour][pr] : 0;
    if (have > caps[k]) return false;                       // I5
  }
  int tb = cnt[Black][PP], tw = cnt[White][PP];
  if (anyPawnSlot && (tb > cb || tw > cw || tb + tw > jj)) return false;   // I4
  for (const Tables::Group& g : t_.groups) {
    int pr = promotesTo(g.role);
    int u = cnt[g.colour][g.role];
    int p = pr >= 0 ? cnt[g.colour][pr] : 0;
    if (g.bound) {
      if (u + p > (int)g.classes.size()) return false;
      if (t_.colour)
        for (int cls = 0; cls < 2; ++cls) {
          int allowed = (int)std::count(g.classes.begin(), g.classes.end(), cls);
          if (onClass[g.colour][g.role][cls] > allowed) return false;
        }
    } else {
      if (u + p < g.minimum || u + p > g.max) return false;
      if (!g.promotable && p) return false;
    }
  }
  return true;
}

// plan.lanes.lane_ok(board, Geometry(setup))
bool Candidate::laneOk(const uint8_t* board) const {
  const int n = v_.n();
  uint32_t trajs[kMaxSquares];
  int ntraj = 0;
  for (int i = 0; i < n; ++i) {
    if (!board[i]) continue;
    Piece p = v_.piece(board[i]);
    if (p.role != P && p.role != L) continue;
    int x = v_.fileOf(i), r0 = wallStart_[p.colour][p.role][x], r1 = v_.rankOf(i);
    uint32_t m = 0;
    for (int r = std::min(r0, r1); r <= std::max(r0, r1); ++r) m |= 1u << v_.idx(x, r);
    trajs[ntraj++] = m;
  }
  for (int i = 0; i < n; ++i) {
    if (!board[i]) continue;
    Piece p = v_.piece(board[i]);
    if (p.role == P || p.role == L) continue;
    int forms[2] = {p.role, -1};
    int uf = unpromotedForm(p.role);
    if (uf >= 0 && v_.inZone(p.colour, v_.rankOf(i))) forms[1] = uf;
    bool ok = false;
    for (int f = 0; f < 2 && !ok; ++f) {
      if (forms[f] < 0) continue;
      const std::vector<uint32_t>& masks = laneMasks_[p.colour][forms[f]];
      const std::vector<int>& off = laneOff_[p.colour][forms[f]];
      for (int k = off[i]; k < off[i + 1] && !ok; ++k) {
        uint32_t S = masks[k];
        bool blocked = false;
        for (int tj = 0; tj < ntraj; ++tj)
          if ((trajs[tj] & ~S) == 0) blocked = true;
        if (!blocked) ok = true;
      }
    }
    if (!ok) return false;
  }
  return true;
}

uint64_t Candidate::index(const uint8_t* board) const {
  const int n = v_.n();
  int u[8] = {}, p[16] = {}, sqOf[16];
  uint32_t confined = 0;
  for (int i = 0; i < n; ++i) {
    uint8_t c = board[i];
    if (!c) continue;
    int fs = fsOfCode_[c];
    if (fs < 0) {
      const Slot& s = slots_[slotOfCode_[c]];
      if (v_.fileOf(i) != s.file || u[s.cs]) return kNoIndex;
      u[s.cs] = v_.rankOf(i);
      confined |= 1u << i;
    } else {
      if (p[fs]) return kNoIndex;
      p[fs] = fsVariantOfCode_[c];
      sqOf[fs] = i;
    }
  }
  uint64_t id = 0;
  for (int k = 0; k < ncs_; ++k) id = id * (uint64_t)(v_.nranks() + 1) + (uint64_t)u[k];
  uint64_t base = ucfgBase_[id];
  if (base == kNoIndex) return kNoIndex;
  uint32_t mask = ucfgMask_[id];
  uint64_t pidx = 0;
  for (size_t f = 0; f < fsSlot_.size(); ++f) {
    const Slot& s = slots_[fsSlot_[f]];
    if (p[f] && s.confined && !(mask & (1u << s.cs))) return kNoIndex;   // both forms of one slot
    pidx = pidx * (uint64_t)fsRadix_[f] + (uint64_t)p[f];
  }
  uint8_t remaining[kMaxSquares];
  int nrem = 0;
  for (int i = 0; i < n; ++i)
    if (!(confined & (1u << i))) remaining[nrem++] = (uint8_t)i;
  uint64_t rank = 0;
  for (size_t f = 0; f < fsSlot_.size(); ++f) {
    if (!p[f]) continue;
    int pos = 0;
    while (remaining[pos] != sqOf[f]) ++pos;
    rank = rank * (uint64_t)nrem + (uint64_t)pos;
    for (int k = pos; k + 1 < nrem; ++k) remaining[k] = remaining[k + 1];
    --nrem;
  }
  return base + offs_[mask][pidx] + rank;
}

int Candidate::flagClass(const State& s) const {
  if (s.flag == kNone) return -1;
  uint8_t c = s.board[s.flag];
  if (!c || v_.colourOf(c) == s.turn) return -1;
  return slotOfCode_[c] % nslotsPerColour_;
}

int Candidate::squareOfSlot(const uint8_t* board, Colour c, int cls) const {
  int slot = (int)c * nslotsPerColour_ + cls;
  for (int i = 0; i < v_.n(); ++i)
    if (board[i] && slotOfCode_[board[i]] == slot) return i;
  return kNone;
}

}  // namespace variant
