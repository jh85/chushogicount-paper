#include "filegame.h"

#include <deque>
#include <unordered_map>

namespace cp {

std::string Slot::repr() const {
  return "Slot(name='" + name + "', colour='" + colour_ch(colour) + "', kind='" + ROLE_NAME[kind] +
         "', start=" + std::to_string(start) + ")";
}

static int group_of(int x) { return (x == 0 || x == 11) ? 0 : (x == 3 || x == 8) ? 1 : 2; }

const std::vector<Slot>& chu_file_slots(int x) {
  static const std::vector<Slot> g[3] = {
      {{"BL", 0, L, 1}, {"BRC", 0, RC, 2}, {"BP", 0, P, 4}, {"WP", 1, P, 9}, {"WRC", 1, RC, 11}, {"WL", 1, L, 12}},
      {{"BP", 0, P, 4}, {"BGB", 0, GB, 5}, {"WGB", 1, GB, 8}, {"WP", 1, P, 9}},
      {{"BP", 0, P, 4}, {"WP", 1, P, 9}}};
  return g[group_of(x)];
}

static bool fz(int colour, int rank) { return colour == 0 ? rank > 12 - 4 : rank <= 4; }

static void dests(const Slot& s, int r, const std::vector<int>& st, std::vector<int>& out) {
  out.clear();
  int d = s.colour == 0 ? 1 : -1;
  int steps[2], ns;
  bool slide;
  if (s.kind == P) { steps[0] = d; ns = 1; slide = false; }
  else if (s.kind == GB) { steps[0] = d; steps[1] = -d; ns = 2; slide = false; }
  else if (s.kind == L) { steps[0] = d; ns = 1; slide = true; }
  else { steps[0] = d; steps[1] = -d; ns = 2; slide = true; }
  auto occ = [&](int b) {
    for (int v : st)
      if (v > 0 && v == b) return true;
    return false;
  };
  for (int k = 0; k < ns; ++k) {
    int b = r + steps[k];
    while (1 <= b && b <= 12 && !occ(b)) {
      out.push_back(b);
      if (!slide) break;
      b += steps[k];
    }
  }
}

static uint64_t enc(const FState& s) {
  uint64_t k = 0;
  for (int v : s) k = k * 16 + (uint64_t)(v + 1);
  return k;
}

std::string rstate(const FState& s) {
  std::string o = "(";
  for (size_t i = 0; i < s.size(); ++i) o += (i ? ", " : "") + std::to_string(s[i]);
  if (s.size() == 1) o += ",";
  return o + ")";
}

// _bfs_tree(slots, 12, 4, strict=True), cached per file group
struct Tree {
  std::unordered_map<uint64_t, std::pair<FState, FMove>> prev;   // state -> (parent, move)
  std::unordered_map<uint64_t, bool> seen;
  FState start;
};

static const Tree& bfs_tree(int x) {
  static Tree trees[3];
  static bool built[3] = {false, false, false};
  int gi = group_of(x);
  if (built[gi]) return trees[gi];
  Tree& t = trees[gi];
  const auto& slots = chu_file_slots(x);
  FState start;
  for (const auto& s : slots) start.push_back(s.start);
  t.start = start;
  t.seen[enc(start)] = true;
  std::deque<FState> q{start};
  std::vector<int> ds;
  while (!q.empty()) {
    FState st = q.front();
    q.pop_front();
    for (size_t i = 0; i < st.size(); ++i) {
      int r = st[i];
      if (r <= 0) continue;
      std::vector<std::pair<FState, FMove>> nxt;
      FState c = st;
      c[i] = CAPTURED;
      nxt.push_back({c, FMove{(int)i, r, CAPTURED, false}});
      dests(slots[i], r, st, ds);
      for (int b : ds) {
        FState m = st;
        m[i] = b;
        nxt.push_back({m, FMove{(int)i, r, b, false}});
        int last = slots[i].colour == 0 ? 12 : 1;
        bool ok = (fz(slots[i].colour, b) && !fz(slots[i].colour, r)) ||
                  ((slots[i].kind == P || slots[i].kind == L) && b == last);
        if (ok) {
          FState pr = st;
          pr[i] = PROMOTED;
          nxt.push_back({pr, FMove{(int)i, r, b, true}});
        }
      }
      for (auto& [ns, fm] : nxt) {
        uint64_t k = enc(ns);
        if (t.seen.count(k)) continue;
        t.seen[k] = true;
        t.prev[k] = {st, fm};
        q.push_back(ns);
      }
    }
  }
  built[gi] = true;
  return t;
}

bool path_to(int x, const FState& target, std::vector<FMove>& out) {
  const Tree& t = bfs_tree(x);
  uint64_t k = enc(target);
  if (!t.seen.count(k)) return false;
  std::vector<FMove> rev;
  FState cur = target;
  while (enc(cur) != enc(t.start)) {
    const auto& pm = t.prev.at(enc(cur));
    rev.push_back(pm.second);
    cur = pm.first;
  }
  std::vector<FMove> fwd(rev.rbegin(), rev.rend());
  out.clear();
  for (const auto& m : fwd)
    if (m.b == CAPTURED && !m.prom) out.push_back(m);
  for (const auto& m : fwd)
    if (!(m.b == CAPTURED && !m.prom)) out.push_back(m);
  return true;
}

// admissible(slots, 12, 4): U-config -> set of promoted-slot sets (bit masks)
using Adm = std::map<std::vector<int>, std::set<unsigned>>;
static const Adm& admissible(int x) {
  static Adm adm[3];
  static bool built[3] = {false, false, false};
  int gi = group_of(x);
  if (built[gi]) return adm[gi];
  const auto& slots = chu_file_slots(x);
  FState start;
  for (const auto& s : slots) start.push_back(s.start);
  std::unordered_map<uint64_t, bool> seen{{enc(start), true}};
  std::vector<FState> stack{start}, all{start};
  std::vector<int> ds;
  while (!stack.empty()) {
    FState st = stack.back();
    stack.pop_back();
    for (size_t i = 0; i < st.size(); ++i) {
      int r = st[i];
      if (r <= 0) continue;
      std::vector<FState> nxt;
      FState c = st;
      c[i] = CAPTURED;
      nxt.push_back(c);
      dests(slots[i], r, st, ds);
      for (int b : ds) {
        FState m = st;
        m[i] = b;
        nxt.push_back(m);
        if (fz(slots[i].colour, r) || fz(slots[i].colour, b)) {
          FState pr = st;
          pr[i] = PROMOTED;
          nxt.push_back(pr);
        }
      }
      for (auto& ns : nxt) {
        uint64_t k = enc(ns);
        if (seen.count(k)) continue;
        seen[k] = true;
        stack.push_back(ns);
        all.push_back(ns);
      }
    }
  }
  for (const auto& st : all) {
    std::vector<int> u;
    unsigned pm = 0;
    for (size_t i = 0; i < st.size(); ++i) {
      u.push_back(st[i] > 0 ? st[i] : 0);
      if (st[i] == PROMOTED) pm |= 1u << i;
    }
    adm[gi][u].insert(pm);
  }
  built[gi] = true;
  return adm[gi];
}

bool file_features(int x, const std::vector<int>& u, FileFeat& out) {
  const auto& slots = chu_file_slots(x);
  const Adm& adm = admissible(x);
  auto it = adm.find(u);
  if (it == adm.end()) return false;
  const auto& fam = it->second;
  int iBP = -1, iWP = -1;
  for (size_t i = 0; i < slots.size(); ++i) {
    if (slots[i].kind == P && slots[i].colour == 0) iBP = (int)i;
    if (slots[i].kind == P && slots[i].colour == 1) iWP = (int)i;
  }
  out.cb = iBP >= 0 && fam.count(1u << iBP);
  out.cw = iWP >= 0 && fam.count(1u << iWP);
  out.j = (out.cb || out.cw) ? 1 : 0;
  if (!out.j) out.cb = out.cw = 0;
  out.elig.clear();
  for (size_t i = 0; i < slots.size(); ++i) {
    if (slots[i].kind == P) continue;
    int e = u[i] ? 0 : (fam.count(1u << i) ? 1 : 0);
    out.elig.push_back({{slots[i].colour, slots[i].kind}, e});
  }
  return true;
}

bool is_candidate_primary(const Board& board) {
  int n[2][NROLES] = {};
  for (int s = 0; s < 144; ++s)
    if (board[s]) n[colour_of(board[s])][role_of(board[s])]++;
  int caps[2][NROLES] = {};
  int cb = 0, cw = 0, jj = 0;
  FileFeat ff;
  for (int x = 0; x < 12; ++x) {
    const auto& slots = chu_file_slots(x);
    std::vector<int> u(slots.size(), 0);
    for (int r = 1; r <= 12; ++r) {
      Piece p = board[SQ(x, r)];
      if (!p) continue;
      int role = role_of(p), c = colour_of(p);
      if (role != P && role != L && role != RC && role != GB) continue;
      int i = -1;
      for (size_t k = 0; k < slots.size(); ++k)
        if (slots[k].colour == c && slots[k].kind == role) i = (int)k;
      if (i < 0 || u[i]) return false;
      u[i] = r;
    }
    if (!file_features(x, u, ff)) return false;
    cb += ff.cb;
    cw += ff.cw;
    jj += ff.j;
    for (auto& [ck, e] : ff.elig) caps[ck.first][ck.second] += e;
  }
  for (int c = 0; c < 2; ++c)
    for (int k : {L, RC, GB}) {
      int promoted = k == L ? pL : k == RC ? pRC : pGB;
      if (n[c][promoted] > caps[c][k]) return false;          // I5
    }
  int tb = n[0][pP], tw = n[1][pP];
  if (tb > cb || tw > cw || tb + tw > jj) return false;        // I4
  for (int c = 0; c < 2; ++c) {
    // Royal (identify): (kings incl. crown prince, elephants)
    int k = n[c][K], e = n[c][E];
    bool ok = (k == 1 && e == 0) || (k == 1 && e == 1) || (k == 2 && e == 0) ||
              (c == 0 && ((k == 0 && e == 0) || (k == 0 && e == 1)));
    if (!ok) return false;
    for (int b : {G, S, C, F, T, M, V, R, H, D})
      if (n[c][b] + n[c][promotes(b)] > 2) return false;
    if (n[c][B] + n[c][pB] > 2) return false;
    int cls[2] = {0, 0};
    for (int s = 0; s < 144; ++s)
      if (board[s] == mk(c, B)) cls[sq_class(s)]++;
    if (cls[0] > 1 || cls[1] > 1) return false;
    if (n[c][O] > 1 || n[c][O] + n[c][N] > 2) return false;
    for (int s = 0; s < 144; ++s)
      if (board[s] == mk(c, O) && sq_class(s) != 1) return false;
    if (n[c][X] > 1 || n[c][X] + n[c][Q] > 2) return false;
  }
  return true;
}

}  // namespace cp
