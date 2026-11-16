// Port of plan/planner.py; comments refer to the Python methods of the same name.
#include "planner.h"

#include <algorithm>
#include <cmath>

namespace cp {

namespace {

bool in_walls(int role) { return role == P || role == L; }
bool in_fluid(int role) { return role == RC || role == GB; }
bool in_confined(int role) { return role == P || role == L || role == RC || role == GB; }
bool in_reversible(int role) {
  switch (role) {
    case K: case Q: case R: case B: case H: case D: case M: case V: case F: case N:
    case pB: case pR: case pM: case pV: case pS: case pC: case pF: case pT:
      return true;
    default:
      return false;
  }
}
SqSet one(int s) {
  SqSet b;
  b.set(s);
  return b;
}
SqSet two(int a, int b) {
  SqSet s;
  s.set(a);
  s.set(b);
  return s;
}
// Python's lst[:n] for an int n of any sign
std::vector<int> head(const std::vector<int>& v, long n) {
  long len = (long)v.size();
  if (n < 0) n = std::max(0L, len + n);
  n = std::min(n, len);
  return std::vector<int>(v.begin(), v.begin() + n);
}
std::vector<int> tail_from(const std::vector<int>& v, long k) {
  long len = (long)v.size();
  if (k < 0) k = std::max(0L, len + k);
  k = std::min(k, len);
  return std::vector<int>(v.begin() + k, v.end());
}
bool contains(const std::vector<int>& v, int x) { return std::find(v.begin(), v.end(), x) != v.end(); }

}  // namespace

Planner::Planner(const OBoard& tgt, Eng& e, int seed, int et, Strategy st, bool df, bool pk)
    : target(tgt), end_turn(et), strategy(st), defer(df), park(pk), eng(e), rng((uint32_t)seed) {
  eng.set_initial();
  sync();
  seen.insert(state());
}

StateKey Planner::key(const Board& b, int t, int f) const {
  StateKey k;
  std::copy(b.begin(), b.end(), k.k.begin());
  k.k[144] = (uint8_t)t;
  k.k[145] = (uint8_t)(f + 1);
  return k;
}

bool Planner::is_wall(int role) const { return in_walls(role) || (in_fluid(role) && !fluid_ok); }

void Planner::sync() { eng.state(board, turn, flag); }

// --- engine interface ---------------------------------------------------------
bool Planner::would_repeat(const PMove& m) {
  if (m.mid >= 0 || m.promote || board[m.to]) return false;
  if (!board[m.from]) key_error(m.from);
  Board nb = board;
  nb[m.to] = nb[m.from];
  nb[m.from] = 0;
  return seen_after(nb, other(turn));
}

void Planner::play(int side, const PMove& m, int retry) {
  if (turn != side)
    throw PyExc{"AssertionError", "('" + cstr(turn) + "', '" + cstr(side) + "', '" + usi(m) + "')"};
  if (retry && would_repeat(m)) {
    perturb(side, m.from);
    while (turn != side) wait(turn);
    if (board[m.to]) throw err("destination of " + usi(m) + " taken while avoiding repetition");
    play(side, m, retry - 1);
    return;
  }
  if (!eng.is_legal(m)) throw err("illegal move " + usi(m) + " for " + cstr(side));
  eng.move(m);
  moves.push_back(usi(m));
  if (moves.size() > 6000) throw err("too many plies");
  sync();
  StateKey st = state();
  if (seen.count(st)) throw Repetition{phase + ": repetition after " + usi(m)};
  seen.insert(st);
}

void Planner::do_(int side, const PMove& m, bool capture) {
  while (turn != side) wait(turn);
  if (!capture && board[m.to]) throw err("destination of " + usi(m) + " was taken by a waiting move");
  play(side, m);
}

void Planner::perturb(int side, int exclude_sq) {
  std::vector<int> ts;
  for (int sq : CANON) {
    Piece p = board[sq];
    if (!p) continue;
    if (colour_of(p) != side || !in_reversible(role_of(p)) || sq == exclude_sq || reserved[sq] || protected_[sq])
      continue;
    single_moves([&](int t) { return board[t]; }, sq, p, ts);
    for (int t : ts) {
      if (board[t] || reserved[t]) continue;
      PMove m = mv(sq, t);
      if (!eng.is_legal(m)) continue;
      Board nb = board;
      nb[t] = nb[sq];
      nb[sq] = 0;
      if (seen_after(nb, other(side))) continue;
      play(side, m, 0);
      pending[side].push_back(mv(t, sq));
      return;
    }
  }
  throw err(std::string("no perturbation available for ") + colour_ch(side));
}

void Planner::wait(int side) {
  if (!pending[side].empty()) {
    PMove m = pending[side].back();
    pending[side].pop_back();
    int a = m.from, b = m.to;
    if (protected_[a] || reserved[b]) {
      pending[side].insert(pending[side].begin(), m);
    } else if (eng.is_legal(m) && !board[b]) {
      Board nb = board;
      nb[b] = nb[a];
      nb[a] = 0;
      if (!seen_after(nb, other(side))) {
        play(side, m);
        return;
      }
      pending[side].push_back(m);
    }
  }
  int lion = lion_sq(side);
  if (lion >= 0 && !seen_after(board, other(side))) {
    for (int m : adjacent_empty(lion)) {
      PMove j = mv(lion, lion, false, m);
      if (eng.is_legal(j)) {
        play(side, j);
        return;
      }
    }
  }
  std::vector<int> ts;
  for (int sq : CANON) {
    Piece p = board[sq];
    if (!p || colour_of(p) != side || !in_reversible(role_of(p))) continue;
    if (reserved[sq] || protected_[sq]) continue;
    single_moves([&](int t) { return board[t]; }, sq, p, ts);
    for (int t : ts) {
      if (board[t] || reserved[t]) continue;
      PMove m = mv(sq, t);
      if (!eng.is_legal(m)) continue;
      Board nb = board;
      nb[t] = nb[sq];
      nb[sq] = 0;
      if (seen_after(nb, other(side))) continue;
      play(side, m);
      pending[side].push_back(mv(t, sq));
      return;
    }
  }
  throw err(std::string("no waiting move for ") + colour_ch(side));
}

// --- board helpers ---------------------------------------------------------------
int Planner::lion_sq(int side) const {
  for (int sq : CANON)
    if (board[sq] == mk(side, N)) return sq;
  return -1;
}

std::vector<int> Planner::adjacent_empty(int sq) const {
  std::vector<int> o;
  for (int t = 0; t < 144; ++t)
    if (cheb(t, sq) == 1 && !board[t]) o.push_back(t);
  return o;
}

std::vector<int> Planner::pieces(int side, int role) const {
  std::vector<int> o;
  for (int sq : CANON) {
    Piece p = board[sq];
    if (p && colour_of(p) == side && (role < 0 || role_of(p) == role)) o.push_back(sq);
  }
  return o;
}

std::vector<int> Planner::empty_squares() const {
  std::vector<int> o;
  for (int s = 0; s < 144; ++s)
    if (!board[s]) o.push_back(s);
  return o;
}

// --- routing -----------------------------------------------------------------------
int Planner::route(int sq, const SqSet& goals, bool capture, bool promote, const SqSet& walls, int depth) {
  if (!board[sq]) throw err("no piece on " + rsq(sq) + " to route");
  protected_.set(sq);
  int res;
  try {
    res = route_(sq, goals, capture, promote, walls, depth);
  } catch (...) {
    protected_.reset(sq);
    throw;
  }
  protected_.reset(sq);
  protected_.reset(res);
  return res;
}

int Planner::route_(int sq, const SqSet& goals, bool capture, bool promote, const SqSet& walls, int depth) {
  int side = colour_of(bat(sq));
  std::vector<int> p;
  if (!path(board, sq, goals, walls, capture, p)) {
    if (depth >= 2) {
      std::vector<int> g;
      for (int s = 0; s < 144 && g.size() < 3; ++s)
        if (goals[s]) g.push_back(s);
      throw err("no route for " + rpiece(bat(sq)) + " from " + rsq(sq) + " to " + rsqlist(g));
    }
    Board ghost{};
    for (int s : CANON) {
      Piece q = board[s];
      if (q && (s == sq || is_wall(role_of(q)) || walls[s] || (capture && goals[s]))) ghost[s] = q;
    }
    if (!path(ghost, sq, goals, walls, capture, p))
      throw err("no route (even through movable pieces) for " + rpiece(bat(sq)) + " from " + rsq(sq));
    std::vector<int> crossed;
    int cur = sq;
    for (int t : p) {
      for (int c : traversed(bat(sq), cur, t)) crossed.push_back(c);
      crossed.push_back(t);
      cur = t;
    }
    SqSet avoid;
    for (int c : crossed) avoid.set(c);
    avoid.set(sq);
    for (int s : crossed)
      if (board[s] && s != sq && !(capture && goals[s])) displace(s, avoid, 0, one(sq));
    if (!board[sq]) throw err("routed piece was displaced");
    return route(sq, goals, capture, promote, walls, depth + 1);
  }
  int cur = sq;
  reserved.reset();
  for (int t : p) reserved.set(t);
  try {
    for (size_t i = 0; i < p.size(); ++i) {
      int t = p[i];
      bool last = i == p.size() - 1;
      if (board[t] && !(capture && last)) {
        reserved.reset();
        return route(cur, goals, capture, promote, walls, depth);
      }
      do_(side, mv(cur, t, promote && last), capture && last);
      protected_.reset(cur);
      cur = t;
      protected_.set(cur);
    }
  } catch (PlannerError& e) {
    protected_.reset(cur);
    reserved.reset();
    if (e.at < 0) e.at = cur;
    throw;
  }
  reserved.reset();
  return cur;
}

void Planner::displace(int sq, const SqSet& avoid, int depth, const SqSet& busy, int replans, int frees) {
  if (replans > 12) throw err("cannot displace " + rpiece(board[sq]) + " from " + rsq(sq) + " (path keeps closing)");
  if (frees > 60) throw err("cannot displace " + rpiece(board[sq]) + " from " + rsq(sq) + " (frontier loop)");
  Piece piece = bat(sq);
  int side = colour_of(piece);
  if (is_wall(role_of(piece))) throw err("cannot displace " + rpiece(piece) + " on " + rsq(sq));
  std::vector<int> goals;
  for (int s : empty_squares())
    if (!avoid[s]) goals.push_back(s);
  std::vector<int> mobile, ts;
  if (park) {
    for (int s : goals) {
      Board after = board;
      after[sq] = 0;
      after[s] = piece;
      single_moves([&](int t) { return after[t]; }, s, piece, ts);
      for (int t : ts)
        if (!after[t]) {
          mobile.push_back(s);
          break;
        }
    }
  }
  if (!mobile.empty()) goals = mobile;
  std::stable_sort(goals.begin(), goals.end(), [&](int a, int b) {
    bool ia = target.has(a), ib = target.has(b);
    if (ia != ib) return ia < ib;
    return cheb(a, sq) < cheb(b, sq);
  });
  std::vector<int> free;
  for (int s : goals)
    if (!target.has(s)) free.push_back(s);
  SqSet w = avoid;
  w.reset(sq);
  std::vector<int> p;
  bool found = false;
  if (!free.empty()) {
    SqSet g;
    for (size_t i = 0; i < free.size() && i < 40; ++i) g.set(free[i]);
    found = path(board, sq, g, w, false, p);
  }
  if (!found) {
    SqSet g;
    for (size_t i = 0; i < goals.size() && i < 60; ++i) g.set(goals[i]);
    found = path(board, sq, g, w, false, p);
  }
  if (!found) {
    SqSet g;
    for (int s : goals) g.set(s);
    found = path(board, sq, g, SqSet(), false, p);
  }
  if (!found) {
    if (depth >= 6) throw err("cannot displace " + rpiece(bat(sq)) + " from " + rsq(sq));
    std::vector<int> fr = frontier(sq);
    for (int t : fr) {
      if (board[t] && !is_wall(role_of(board[t])) && !busy[t]) {
        SqSet a2 = avoid, b2 = busy;
        a2.set(sq);
        b2.set(sq);
        try {
          displace(t, a2, depth + 1, b2);
        } catch (PlannerError&) {
          continue;
        }
        if (!board[sq]) throw err("displaced piece vanished");
        displace(sq, avoid, depth, busy, replans, frees + 1);
        return;
      }
    }
    throw err("cannot displace " + rpiece(bat(sq)) + " from " + rsq(sq) + " (jammed)");
  }
  int cur = sq;
  reserved = avoid;
  for (int t : p) reserved.set(t);
  for (int t : p) {
    if (board[t]) {
      reserved.reset();
      displace(cur, avoid, depth, busy, replans + 1, frees);
      return;
    }
    do_(side, mv(cur, t));
    cur = t;
  }
  reserved.reset();
}

void Planner::rescue_trapped(int frm, int to, const SqSet& segment) {
  if (!board[frm]) key_error(frm);
  std::vector<std::pair<int, Piece>> items;
  for (int sq : CANON)
    if (board[sq]) items.push_back({sq, board[sq]});
  std::vector<int> ts;
  for (auto [sq, piece] : items) {
    if (sq == frm || is_wall(role_of(piece)) || sq == to || board[sq] != piece) continue;
    if (!board[frm]) key_error(frm);
    Board after = board;
    after[to] = after[frm];
    after[frm] = 0;
    bool now = false, later = false;
    single_moves([&](int t) { return board[t]; }, sq, board[sq], ts);
    for (int t : ts)
      if (!board[t]) now = true;
    single_moves([&](int t) { return after[t]; }, sq, after[sq], ts);
    for (int t : ts)
      if (!after[t]) later = true;
    if (now && !later) {
      SqSet av = segment;
      for (int t = 0; t < 144; ++t)
        if (cheb(t, to) <= 1) av.set(t);
      try {
        displace(sq, av, 0, one(frm));
      } catch (PlannerError&) {
      }
      if (board[frm] != after[to]) throw err("wall piece displaced during rescue");
    }
  }
}

std::vector<int> Planner::frontier(int sq) {
  Piece piece = bat(sq);
  PySquareSet region;
  region.add(sq);
  std::vector<int> stack{sq}, ts;
  Board b = board;
  b[sq] = 0;
  while (!stack.empty()) {
    int cur = stack.back();
    stack.pop_back();
    single_moves([&](int t) { return b[t]; }, cur, piece, ts);
    for (int t : ts)
      if (!b[t] && !region.contains(t)) {
        region.add(t);
        stack.push_back(t);
      }
  }
  std::vector<int> keys;
  int val[144];
  std::fill(val, val + 144, -1);
  for (int cur : region.items()) {
    adjacent_dests(cur, piece, ts);
    for (int t : ts)
      if (board[t] && t != sq) {
        int d = cheb(t, sq);
        if (val[t] < 0) {
          keys.push_back(t);
          val[t] = std::min(99, d);
        } else {
          val[t] = std::min(val[t], d);
        }
      }
  }
  std::stable_sort(keys.begin(), keys.end(), [&](int a, int b) { return val[a] < val[b]; });
  return keys;
}

int Planner::into_zone(int sq, int tries, int cls) {
  if (!board[sq]) throw err("no piece on " + rsq(sq) + " to promote");
  int side = colour_of(board[sq]), role = role_of(board[sq]);
  if (tries > 5) throw err("cannot bring " + rpiece(board[sq]) + " at " + rsq(sq) + " into the zone");
  if (in_zone(side, sq)) {
    SqSet out;
    for (int s : empty_squares())
      if (!in_zone(side, s)) out.set(s);
    sq = route(sq, out);
  }
  protected_.set(sq);
  bool bound = role == B || role == O || role == pF;
  auto movable = [&](int q) { return !board[q] || !is_wall(role_of(board[q])); };
  bool have = false;
  std::pair<int, int> best_score;
  int bst = -1, bz = -1;
  std::vector<int> bcrossed, zs;
  Piece me = mk(side, role);
  for (int st = 0; st < 144; ++st) {
    if (in_zone(side, st) || (bound && sq_class(st) != sq_class(sq)) || !movable(st)) continue;
    single_moves([](int) -> Piece { return 0; }, st, me, zs);
    for (int z : zs) {
      if (!in_zone(side, z) || !movable(z) || (cls >= 0 && sq_class(z) != cls)) continue;
      std::vector<int> crossed = traversed(me, st, z);
      bool ok = true;
      for (int c : crossed)
        if (!movable(c)) ok = false;
      if (!ok) continue;
      int blockers = 0;
      std::vector<int> all = crossed;
      all.push_back(st);
      all.push_back(z);
      for (int c : all)
        if (board[c] && c != sq) ++blockers;
      std::pair<int, int> score{blockers, cheb(sq, st)};
      if (!have || score < best_score) {
        have = true;
        best_score = score;
        bst = st;
        bz = z;
        bcrossed = crossed;
      }
    }
  }
  if (!have) {
    protected_.reset(sq);
    throw err("no entry line for " + rpiece(bat(sq)) + " at " + rsq(sq));
  }
  int st = bst, z = bz;
  SqSet avoid;
  for (int c : bcrossed) avoid.set(c);
  avoid.set(st);
  avoid.set(z);
  std::vector<int> all = bcrossed;
  all.push_back(st);
  all.push_back(z);
  try {
    for (int c : all)
      if (board[c] && c != sq) displace(c, avoid, 0, one(sq));
  } catch (...) {
    protected_.reset(sq);
    throw;
  }
  protected_.reset(sq);
  if (!board[sq]) throw err("promoting piece was displaced");
  if (st != sq) {
    SqSet w = avoid;
    w.reset(st);
    try {
      st = route(sq, one(st), false, false, w);
    } catch (PlannerError& e) {
      st = route(e.at >= 0 ? e.at : sq, one(st));
    }
  }
  bool blocked = board[z] != 0;
  for (int c : bcrossed)
    if (board[c]) blocked = true;
  if (blocked) return into_zone(st, tries + 1, cls);
  do_(side, mv(st, z, true));
  SqSet parkset;
  for (int s : empty_squares())
    if (!in_zone(side, s) && (side == 0 ? SR(s) <= 7 : SR(s) >= 6)) parkset.set(s);
  if (parkset.none())
    for (int s : empty_squares())
      if (!in_zone(side, s)) parkset.set(s);
  try {
    return route(z, parkset);
  } catch (PlannerError&) {
    return z;
  }
}

void Planner::capture(int victim) {
  Piece v = bat(victim);
  int side = other(colour_of(v));
  int lion = lion_sq(side);
  if (lion < 0) throw err(cstr(side) + " has no lion to capture " + rpiece(v) + " on " + rsq(victim));
  if (role_of(v) == N) {
    SqSet pre;
    for (int s : empty_squares())
      if (cheb(s, victim) == 1) pre.set(s);
    route(lion, pre);
    lion = lion_sq(side);
    if (lion < 0) throw PyExc{"TypeError", "'NoneType' object is not subscriptable"};
    do_(side, mv(lion, victim), true);
    return;
  }
  route(lion, one(victim), true);
}

// --- the plan ------------------------------------------------------------------------
std::vector<std::string> Planner::run() {
  phase = "0-lions-out";
  do_(0, mv(SQ(5, 3), SQ(5, 5)));
  do_(1, mv(SQ(6, 10), SQ(6, 8)));

  for (int s : target.order) tcount[colour_of(target.a[s])][role_of(target.a[s])]++;
  phase = "A-captures";
  std::vector<int> victims;
  for (int x = 0; x < 12; ++x) {
    const auto& slots = chu_file_slots(x);
    std::vector<int> u(slots.size(), 0);
    for (size_t i = 0; i < slots.size(); ++i)
      for (int r = 1; r <= 12; ++r)
        if (target.a[SQ(x, r)] == mk(slots[i].colour, slots[i].kind)) u[i] = r;
    file_u[x] = u;
  }
  std::vector<int> assign[2][NROLES];
  assign_promoted(assign);
  for (int x = 0; x < 12; ++x) {
    const auto& slots = chu_file_slots(x);
    for (size_t i = 0; i < slots.size(); ++i)
      if (file_u[x][i] == 0 && !contains(assign[slots[i].colour][slots[i].kind], x))
        victims.push_back(SQ(x, slots[i].start));
  }
  doomed_lions.clear();
  last_royal = false;
  for (int side = 0; side < 2; ++side) {
    for (int base : {G, S, C, F, T, M, V, R, H, D, B}) {
      int keep = tcount[side][base] + tcount[side][promotes(base)];
      std::vector<int> have = pieces(side, base);
      if (base == B) {
        std::vector<int> want_cls;
        for (int q : target.order)
          if (target.a[q] == mk(side, B)) want_cls.push_back(sq_class(q));
        std::stable_sort(have.begin(), have.end(), [&](int a, int b) {
          return (int)!contains(want_cls, sq_class(a)) < (int)!contains(want_cls, sq_class(b));
        });
        for (int q : tail_from(have, keep)) victims.push_back(q);
        continue;
      }
      std::vector<int> srt = have;
      std::stable_sort(srt.begin(), srt.end(), [](int a, int b) {
        return -std::fabs(SR(a) - 6.5) < -std::fabs(SR(b) - 6.5);
      });
      for (int q : head(srt, (long)have.size() - keep)) victims.push_back(q);
    }
    for (auto [uname, pname] : {std::pair<int, int>{O, N}, std::pair<int, int>{X, Q}}) {
      int k = tcount[side][uname], big = tcount[side][pname];
      if (k == 0 && big <= 1)
        for (int q : pieces(side, uname)) victims.push_back(q);
      if (big == 0 && pname == N) doomed_lions.push_back(side);
      if (big == 0 && pname == Q)
        for (int q : pieces(side, pname)) victims.push_back(q);
    }
    int kings = tcount[side][K], e = tcount[side][E];
    if (kings == 1 && e == 0)
      for (int q : pieces(side, E)) victims.push_back(q);
    if (kings == 0) {
      if (side == 1) throw err("White has no royal in the target");
      if (e == 0)
        for (int q : pieces(side, E)) victims.push_back(q);
      last_royal = true;
    }
  }
  for (int v : victims)
    if (board[v]) capture(v);

  phase = "B-files";
  deferred.clear();
  for (int x = 0; x < 12; ++x) {
    const auto& slots = chu_file_slots(x);
    const auto& u = file_u[x];
    FState state;
    for (size_t i = 0; i < slots.size(); ++i)
      state.push_back(u[i] ? u[i] : (contains(assign[slots[i].colour][slots[i].kind], x) ? PROMOTED : CAPTURED));
    std::vector<FMove> play;
    if (!path_to(x, state, play))
      throw err("file " + std::to_string(x) + ": no abstract play to " + rstate(state));
    bool any_prom = false;
    for (const auto& m : play)
      if (m.prom) any_prom = true;
    for (size_t pi = 0; pi < play.size(); ++pi) {
      const FMove fm = play[pi];
      if (fm.b == CAPTURED && !fm.prom) continue;
      const Slot& s = slots[fm.i];
      int frm = SQ(x, fm.a), to = SQ(x, fm.b);
      if (board[frm] != mk(s.colour, s.kind))
        throw err("file " + std::to_string(x) + ": expected " + s.repr() + " on " + rsq(frm) + ", found " +
                  rpiece(board[frm]));
      int step = fm.b > fm.a ? 1 : -1;
      SqSet segment;
      for (int rr = std::min(fm.a, fm.b); rr <= std::max(fm.a, fm.b); ++rr) segment.set(SQ(x, rr));
      for (int r = fm.a + step; r != fm.b + step; r += step)
        if (board[SQ(x, r)]) displace(SQ(x, r), segment);
      if (defer && in_walls(s.kind) && !fm.prom && seals_entrance(to) && !any_prom) {
        size_t idx = 0;
        while (!(play[idx] == fm)) ++idx;
        Deferred d{x, fm.i, {}};
        for (size_t k = idx; k < play.size(); ++k)
          if (!(play[k].b == CAPTURED && !play[k].prom)) d.moves.push_back(play[k]);
        deferred.push_back(d);
        break;
      }
      if (in_walls(s.kind) && !fm.prom) rescue_trapped(frm, to, segment);
      reserved = segment;
      for (int r = fm.a + step; r != fm.b + step; r += step)
        if (board[SQ(x, r)]) displace(SQ(x, r), segment);
      reserved = segment;
      do_(s.colour, mv(frm, to, fm.prom));
      reserved.reset();
    }
  }

  phase = "C-promotions";
  for (int side = 0; side < 2; ++side) {
    for (int base : {G, S, C, F, T, M, V, R, H, D, B, E, O, X}) {
      int prom = promotes(base);
      int want = tcount[side][prom];
      if (prom == N || prom == Q || prom == K) want = want == 2 ? 1 : 0;
      for (int w = 0; w < want; ++w) {
        std::vector<int> cands = pieces(side, base);
        if (cands.empty())
          throw err(std::string("no ") + colour_ch(side) + " " + ROLE_NAME[base] + " left to promote");
        std::stable_sort(cands.begin(), cands.end(), [&](int a, int b) {
          return side == 0 ? -SR(a) < -SR(b) : SR(a) < SR(b);
        });
        if (base == B) {
          std::vector<int> want_cls;
          for (int q : target.order)
            if (target.a[q] == mk(side, B)) want_cls.push_back(sq_class(q));
          std::stable_sort(cands.begin(), cands.end(), [&](int a, int b) {
            return (int)contains(want_cls, sq_class(a)) < (int)contains(want_cls, sq_class(b));
          });
        }
        int cls = -1;
        if (prom == pF) {
          std::vector<int> want_cls;
          for (int q : target.order)
            if (target.a[q] == mk(side, pF)) want_cls.push_back(sq_class(q));
          for (int q : pieces(side, pF)) {
            auto it = std::find(want_cls.begin(), want_cls.end(), sq_class(q));
            if (it == want_cls.end()) throw PyExc{"ValueError", "list.remove(x): x not in list"};
            want_cls.erase(it);
          }
          if (want_cls.empty()) throw PyExc{"IndexError", "list index out of range"};
          cls = want_cls[0];
        }
        into_zone(cands[0], 0, cls);
      }
    }
  }

  phase = "D-placement";
  fluid_ok = true;
  auto reservedc = reserve_capturers();
  SqSet excl;
  for (auto& r : reservedc) excl.set(r.second.second);
  if (last_royal) {
    std::vector<int> opts;
    for (int q : target.order) {
      Piece p = target.a[q];
      if (colour_of(p) == 1 && !in_confined(role_of(p)) && role_of(p) != N) opts.push_back(q);
    }
    auto openn = [&](int q) {
      int n = 0;
      for (int t = 0; t < 144; ++t)
        if (cheb(t, q) == 1 && !target.has(t)) ++n;
      return -n;
    };
    std::stable_sort(opts.begin(), opts.end(), [&](int a, int b) { return openn(a) < openn(b); });
    if (opts.empty()) throw err("terminal: no White capturer");
    terminal_sq = opts[0];
    excl.set(terminal_sq);
  }
  place_all(excl);
  if (run_deferred()) place_all(excl);

  phase = "E-finish";
  for (int side : doomed_lions) {
    int capturer_target = -1;
    for (auto& r : reservedc)
      if (r.first == side) capturer_target = r.second.second;
    Piece piece = tat(capturer_target);
    std::vector<int> cands;
    for (int q : CANON)
      if (board[q] == piece && target.a[q] != piece) cands.push_back(q);
    std::vector<int> ts, ts2;
    if (cands.empty() && board[capturer_target] == piece) {
      single_moves([&](int t) { return board[t]; }, capturer_target, piece, ts);
      for (int t : ts) {
        if (board[t]) continue;
        Board b2 = board;
        b2[t] = b2[capturer_target];
        b2[capturer_target] = 0;
        single_moves([&](int q) { return b2[q]; }, t, b2[t], ts2);
        if (contains(ts2, capturer_target)) {
          do_(colour_of(piece), mv(capturer_target, t));
          cands = {t};
          break;
        }
      }
    }
    if (cands.empty()) throw err("capturer " + rpiece(piece) + " not found");
    int cap_sq = cands[0];
    int lion = lion_sq(side);
    if (lion < 0) throw err(cstr(side) + " lion already gone");
    if (lion != capturer_target) route(lion, one(capturer_target));
    flush();
    if (turn != other(side)) wait(turn);
    flush();
    route(cap_sq, one(capturer_target), true);
  }
  if (last_royal) {
    place_all(one(terminal_sq));
    terminal_capture();
    verify();
    return moves;
  }
  place_all(SqSet());
  for (int k = 0; k < 12; ++k) {
    flush();
    if (flag < 0 && turn == end_turn && pending[0].empty() && pending[1].empty()) break;
    wait(turn);
  }
  fix_parity(end_turn);
  verify();
  return moves;
}

void Planner::assign_promoted(std::vector<int> assign[2][NROLES]) {
  FileFeat ff;
  std::vector<FileFeat> feats(12);
  for (int x = 0; x < 12; ++x) {
    if (!file_features(x, file_u[x], ff))
      throw PlannerError{"A-captures", "file " + std::to_string(x) + " U-config not admissible", -1};
    feats[x] = ff;
  }
  auto elig = [&](int x, int c, int k) {
    for (auto& [ck, e] : feats[x].elig)
      if (ck.first == c && ck.second == k) return e;
    return 0;
  };
  for (int side = 0; side < 2; ++side)
    for (int kind : {L, RC, GB}) {
      int need = tcount[side][promotes(kind)];
      std::vector<int> files;
      for (int x = 0; x < 12; ++x)
        if (elig(x, side, kind)) files.push_back(x);
      if ((int)files.size() < need)
        throw PlannerError{"A-captures",
                           std::string("not enough eligible files for ") + colour_ch(side) + " +" + ROLE_NAME[kind], -1};
      assign[side][kind] = std::vector<int>(files.begin(), files.begin() + need);
    }
  std::vector<int> free_files;
  for (int x = 0; x < 12; ++x)
    if (feats[x].j) free_files.push_back(x);
  for (int side = 0; side < 2; ++side) {
    int need = tcount[side][pP];
    if ((int)free_files.size() < need)
      throw PlannerError{"A-captures", std::string("not enough pawn-free files for ") + colour_ch(side) + " tokins", -1};
    assign[side][P] = std::vector<int>(free_files.begin(), free_files.begin() + need);
    free_files.erase(free_files.begin(), free_files.begin() + need);
  }
}

std::vector<std::pair<int, std::pair<int, int>>> Planner::reserve_capturers() {
  std::vector<std::pair<int, std::pair<int, int>>> out;
  for (int side : doomed_lions) {
    int enemy = other(side);
    bool have = false;
    std::pair<int, int> best;
    for (int sq : CANON) {
      Piece p = board[sq];
      if (!p) continue;
      int c = colour_of(p), role = role_of(p);
      if (c != enemy || role == N || role == K || in_confined(role) || role == pP || role == pGB || role == pL ||
          role == pRC)
        continue;
      int tgt = target_for(sq);
      if (tgt < 0) continue;
      if (!have || role == Q || role == R || role == pR || role == D || role == pB || role == H) {
        best = {sq, tgt};
        have = true;
      }
    }
    if (!have) throw PlannerError{"D-placement", std::string("no capturer available for the ") + colour_ch(side) + " lion", -1};
    out.push_back({side, best});
  }
  return out;
}

int Planner::target_for(int sq) {
  Piece piece = bat(sq);
  int role = role_of(piece);
  if (in_walls(role)) return sq;
  if (in_fluid(role)) {
    std::vector<int> want;
    for (int s : target.order)
      if (target.a[s] == piece && SX(s) == SX(sq)) want.push_back(s);
    if (want.size() != 1) throw err("no target for " + rpiece(piece) + " on file " + std::to_string(SX(sq)));
    return want[0];
  }
  std::vector<int> want, have;
  for (int s : target.order)
    if (target.a[s] == piece) want.push_back(s);
  for (int s : CANON)
    if (board[s] == piece) have.push_back(s);
  int extra = (piece == mk(0, K) && last_royal) ? 1 : 0;
  if (want.size() + extra != have.size())
    throw err("material mismatch for " + rpiece(piece) + ": have " + std::to_string(have.size()) + ", want " +
              std::to_string(want.size()));
  bool bound = role == B || role == O || role == pF;
  std::vector<std::array<int, 3>> pairs;
  for (int a : have)
    for (int b : want)
      if (!bound || sq_class(a) == sq_class(b)) pairs.push_back({cheb(a, b), a, b});
  std::sort(pairs.begin(), pairs.end());
  SqSet ua, ub;
  int match = -1;
  for (auto& pr : pairs) {
    int a = pr[1], b = pr[2];
    if (!ua[a] && !ub[b]) {
      if (a == sq) match = b;
      ua.set(a);
      ub.set(b);
    }
  }
  if (match < 0) {
    if (extra) return -1;
    throw err("no colour-consistent target for " + rpiece(piece) + " on " + rsq(sq));
  }
  return match;
}

std::vector<std::pair<int, bool>> Planner::peel_order(const SqSet& excluded) {
  std::vector<int> remaining;
  for (int s : target.order)
    if (!in_walls(role_of(target.a[s])) && !excluded[s]) remaining.push_back(s);
  Board obstacles = target.a;
  std::vector<std::pair<int, bool>> order;
  std::vector<int> ts;
  while (!remaining.empty()) {
    int best_size = -1, best_sq = -1;
    for (int sq : remaining) {
      Piece piece = target.a[sq];
      Board b = obstacles;
      b[sq] = 0;
      SqSet region;
      region.set(sq);
      int count = 1;
      std::vector<int> stack{sq};
      while (!stack.empty() && count < 40) {
        int cur = stack.back();
        stack.pop_back();
        reverse_moves([&](int t) { return b[t]; }, cur, piece, ts);
        for (int t : ts)
          if (!region[t]) {
            region.set(t);
            ++count;
            stack.push_back(t);
          }
      }
      if (count > best_size) {
        best_size = count;
        best_sq = sq;
      }
    }
    order.push_back({best_sq, best_size < 12});
    remaining.erase(std::find(remaining.begin(), remaining.end(), best_sq));
    obstacles[best_sq] = 0;
  }
  std::reverse(order.begin(), order.end());
  return order;
}

int Planner::instance_for(int tgt, const SqSet& inserted, const SqSet& skip) {
  Piece piece = tat(tgt);
  int role = role_of(piece);
  bool bound = role == B || role == O || role == pF;
  std::vector<int> cands;
  for (int q : CANON)
    if (board[q] == piece && !inserted[q] && !skip[q] && !(bound && sq_class(q) != sq_class(tgt)))
      if (!in_fluid(role) || SX(q) == SX(tgt)) cands.push_back(q);
  if (cands.empty()) throw err("no free instance of " + rpiece(piece) + " for " + rsq(tgt));
  int best = cands[0];
  for (int q : cands)
    if (cheb(q, tgt) < cheb(best, tgt)) best = q;
  return best;
}

static SqSet to_sqset(const PySquareSet& s) {
  SqSet b;
  for (int k : s.items()) b.set(k);
  return b;
}

void Planner::place_all_peel(const SqSet& excluded) {
  SqSet ex = excluded | blocked_targets();
  auto order = peel_order(ex);
  PySquareSet inserted;
  std::vector<std::pair<int, bool>> queue(order.begin(), order.end());
  int attempts[144] = {};
  while (!queue.empty()) {
    auto [tgt, needs_buffer] = queue.front();
    queue.erase(queue.begin());
    auto requeue = [&]() {
      queue.insert(queue.begin() + std::min<size_t>(3, queue.size()), {tgt, needs_buffer});
    };
    if (board[tgt] == tat(tgt)) {
      inserted.add(tgt);
      continue;
    }
    if (++attempts[tgt] > 6) throw err("placement did not converge at " + rsq(tgt));
    SqSet ins = to_sqset(inserted);
    int sq = instance_for(tgt, ins);
    SqSet walls = ins;
    if (board[tgt]) {
      SqSet av = walls;
      av.set(tgt);
      try {
        displace(tgt, av, 0, one(sq));
      } catch (PlannerError&) {
      }
      if (board[tgt] || board[sq] != tat(tgt)) {
        requeue();
        continue;
      }
    }
    bool skip_rest = false;
    try {
      route(sq, one(tgt), false, false, walls);
    } catch (PlannerError& e) {
      sq = e.at >= 0 ? e.at : sq;
      if (board[sq] != tat(tgt)) {
        requeue();
        skip_rest = true;
      } else {
        PySquareSet before = PySquareSet::copy_of(inserted);
        bool ok = true;
        try {
          route(sq, one(tgt));
        } catch (PlannerError&) {
          requeue();
          ok = false;
        }
        if (!ok) {
          skip_rest = true;
        } else {
          for (int u : before.items())
            if (board[u] != tat(u)) {
              inserted.discard(u);
              queue.insert(queue.begin(), {u, false});
            }
        }
      }
    }
    if (skip_rest) continue;
    if (board[tgt] == tat(tgt))
      inserted.add(tgt);
    else
      requeue();
    for (int u : inserted.items())
      if (board[u] != tat(u)) {
        inserted.discard(u);
        queue.push_back({u, false});
      }
  }
}

void Planner::place_all_greedy(const SqSet& excluded) {
  auto openness = [&](int t) {
    int n = 0;
    for (int u = 0; u < 144; ++u)
      if (cheb(u, t) == 1 && !target.has(u)) ++n;
    return n;
  };
  for (int it = 0; it < 400; ++it) {
    std::vector<int> todo;
    for (int sq : CANON) {
      Piece p = board[sq];
      if (!p) continue;
      if (in_walls(role_of(p))) continue;
      if (role_of(p) == N && contains(doomed_lions, colour_of(p))) continue;
      if (target_for(sq) != sq) todo.push_back(sq);
    }
    SqSet blocked = blocked_targets();
    std::vector<int> t3;
    for (int sq : todo) {
      int t = target_for(sq);
      if (t < 0) continue;
      if (!excluded[t] && !blocked[t]) t3.push_back(sq);
    }
    todo = t3;
    if (todo.empty()) return;
    if (it < 3) {
      std::vector<std::pair<int, int>> keyed;
      for (int sq : todo) keyed.push_back({openness(target_for(sq)), sq});
      std::stable_sort(keyed.begin(), keyed.end(),
                       [](const std::pair<int, int>& a, const std::pair<int, int>& b) { return a.first < b.first; });
      for (size_t i = 0; i < todo.size(); ++i) todo[i] = keyed[i].second;
    } else {
      rng.shuffle(todo);
    }
    bool progressed = false;
    std::vector<std::pair<int, Piece>> items;
    for (int sq : todo) items.push_back({sq, board[sq]});
    for (auto [sq0, piece] : items) {
      int sq = sq0;
      if (board[sq] != piece) continue;
      int tgt = target_for(sq);
      if (tgt == sq || tgt < 0) continue;
      SqSet placed;
      for (int u : CANON) {
        Piece p = board[u];
        if (p && target.a[u] == p && !in_walls(role_of(p)) && u != tgt) placed.set(u);
      }
      if (board[tgt]) {
        if (in_walls(role_of(board[tgt]))) throw err("target " + rsq(tgt) + " holds a confined piece");
        SqSet av = placed;
        av.set(tgt);
        try {
          displace(tgt, av, 0, one(sq));
        } catch (PlannerError&) {
          continue;
        }
        if (!board[sq]) continue;
      }
      try {
        route(sq, one(tgt), false, false, placed);
        progressed = true;
      } catch (PlannerError& e) {
        sq = e.at >= 0 ? e.at : sq;
        if (board[sq] != piece) continue;
        try {
          route(sq, one(tgt));
          progressed = true;
        } catch (PlannerError&) {
          continue;
        }
      }
    }
    if (!progressed) {
      std::vector<int> q;
      for (auto [s, p] : items) {
        (void)p;
        if (board[s] && !in_walls(role_of(board[s]))) {
          int t = target_for(s);
          if (t != s && t >= 0) q.push_back(s);
        }
      }
      if (q.empty()) continue;
      route(q[0], one(target_for(q[0])));
    }
  }
  throw err("placement did not converge");
}

bool Planner::seals_entrance(int sq) {
  std::vector<int> ts;
  for (int t : target.order) {
    Piece piece = target.a[t];
    if (in_walls(role_of(piece)) || cheb(t, sq) > 2) continue;
    Board fin = target.a;
    fin[t] = 0;
    fin[sq] = 0;
    reverse_moves([&](int q) { return fin[q]; }, t, piece, ts);
    if (contains(ts, sq)) {
      fin[sq] = mk(1, P);
      reverse_moves([&](int q) { return fin[q]; }, t, piece, ts);
      if (ts.empty()) return true;
    }
  }
  return false;
}

bool Planner::run_deferred() {
  bool done = false;
  for (const auto& d : deferred) {
    const auto& slots = chu_file_slots(d.x);
    for (const auto& m : d.moves) {
      const Slot& sl = slots[m.i];
      int a = m.a, b = m.b, x = d.x;
      int frm = SQ(x, a), to = SQ(x, b);
      if (board[frm] != mk(sl.colour, sl.kind)) throw err("deferred: expected " + sl.repr() + " on " + rsq(frm));
      int step = b > a ? 1 : -1;
      SqSet segment;
      for (int rr = std::min(a, b); rr <= std::max(a, b); ++rr) segment.set(SQ(x, rr));
      reserved = segment;
      for (int r = a + step; r != b + step; r += step)
        if (board[SQ(x, r)]) displace(SQ(x, r), segment, 0, one(frm));
      reserved = segment;
      do_(sl.colour, mv(frm, to, m.prom));
      reserved.reset();
      done = true;
    }
  }
  deferred.clear();
  return done;
}

SqSet Planner::blocked_targets() const {
  SqSet b;
  for (int t : target.order)
    if (board[t] && is_wall(role_of(board[t])) && board[t] != target.a[t]) b.set(t);
  return b;
}

std::vector<int> Planner::entrances(int tgt, Piece piece, const SqSet& inserted) {
  Board b{};
  for (int q : CANON)
    if (board[q] && (inserted[q] || is_wall(role_of(board[q])))) b[q] = board[q];
  b[tgt] = 0;
  std::vector<int> ts, out;
  reverse_moves([&](int q) { return b[q]; }, tgt, piece, ts);
  for (int a : ts)
    if (!inserted[a]) out.push_back(a);
  return out;
}

void Planner::place_all_edge(const SqSet& excluded) {
  std::vector<int> targets;
  for (int s : target.order)
    if (!in_walls(role_of(target.a[s])) && !excluded[s]) targets.push_back(s);
  int attempts[144] = {};
  while (true) {
    SqSet blocked = blocked_targets();
    std::vector<int> todo;
    SqSet inserted;
    for (int t : targets) {
      if (board[t] != target.a[t] && !blocked[t]) todo.push_back(t);
      if (board[t] == target.a[t]) inserted.set(t);
    }
    if (todo.empty()) return;
    std::vector<std::array<int, 3>> scored;
    for (int t : todo) {
      auto ent = entrances(t, target.a[t], inserted);
      scored.push_back({ent.empty() ? 1 : 0, (int)ent.size(), t});
    }
    std::sort(scored.begin(), scored.end());
    int tgt = scored[0][2];
    if (++attempts[tgt] > 8) throw err("placement did not converge at " + rsq(tgt));
    int sq = instance_for(tgt, inserted);
    SqSet walls = inserted;
    if (board[tgt]) {
      SqSet av = walls;
      av.set(tgt);
      try {
        displace(tgt, av, 0, one(sq));
      } catch (PlannerError&) {
      }
      if (board[tgt] || board[sq] != tat(tgt)) continue;
    }
    try {
      route(sq, one(tgt), false, false, walls);
    } catch (PlannerError& e) {
      sq = e.at >= 0 ? e.at : sq;
      if (board[sq] != tat(tgt)) continue;
      try {
        route(sq, one(tgt));
      } catch (PlannerError&) {
        continue;
      }
    }
  }
}

SqSet Planner::approach(int tgt, Piece piece, const SqSet& inserted, size_t cap) {
  Board b{};
  for (int q : CANON)
    if (board[q] && is_wall(role_of(board[q]))) b[q] = board[q];
  for (int q = 0; q < 144; ++q)
    if (inserted[q]) b[q] = tat(q);
  b[tgt] = 0;
  SqSet region;
  region.set(tgt);
  size_t count = 1;
  std::vector<int> stack{tgt}, ts;
  while (!stack.empty() && count <= cap) {
    int cur = stack.back();
    stack.pop_back();
    reverse_moves([&](int q) { return b[q]; }, cur, piece, ts);
    for (int t : ts)
      if (!region[t] && !inserted[t]) {
        region.set(t);
        ++count;
        stack.push_back(t);
      }
  }
  region.reset(tgt);
  return region;
}

void Planner::place_all_deps(const SqSet& excluded) {
  const int OPEN = 12;
  std::vector<int> targets;
  for (int s : target.order)
    if (!in_walls(role_of(target.a[s])) && !excluded[s]) targets.push_back(s);
  int attempts[144] = {};
  while (true) {
    SqSet blocked = blocked_targets();
    SqSet inserted;
    for (int t : targets)
      if (board[t] == target.a[t]) inserted.set(t);
    std::vector<int> todo;
    for (int t : targets)
      if (!inserted[t] && !blocked[t]) todo.push_back(t);
    if (todo.empty()) return;
    std::vector<SqSet> regions(144);
    for (int t : todo) regions[t] = approach(t, target.a[t], inserted);
    std::vector<std::array<int, 5>> scored;
    for (int t : todo) {
      int r = (int)regions[t].count();
      if (r == 0) {
        scored.push_back({3, 0, 0, 0, t});
        continue;
      }
      int closes = 0;
      for (int u : todo)
        if (u != t && regions[u][t] && (int)regions[u].count() >= OPEN) {
          SqSet i2 = inserted;
          i2.set(t);
          if ((int)approach(u, target.a[u], i2).count() < OPEN) ++closes;
        }
      int urgent = r < OPEN ? 0 : 1;
      int edge = std::min({SX(t), 11 - SX(t), SR(t) - 1, 12 - SR(t)});
      scored.push_back({urgent, closes, r, edge, t});
    }
    std::sort(scored.begin(), scored.end());
    int tgt = scored[0][4];
    if (++attempts[tgt] > 8) throw err("placement did not converge at " + rsq(tgt));
    SqSet skip;
    for (int k = 0; k < 3; ++k) {
      int sq;
      try {
        sq = instance_for(tgt, inserted, skip);
      } catch (PlannerError&) {
        if (skip.none()) throw;
        break;
      }
      skip.set(sq);
      SqSet walls = inserted;
      if (board[tgt]) {
        SqSet av = walls;
        av.set(tgt);
        try {
          displace(tgt, av, 0, one(sq));
        } catch (PlannerError&) {
        }
        if (board[tgt] || board[sq] != tat(tgt)) break;
      }
      bool done = false, again = false;
      try {
        route(sq, one(tgt), false, false, walls);
        done = true;
      } catch (PlannerError& e) {
        int at = e.at >= 0 ? e.at : sq;
        if (board[at] != tat(tgt)) {
          done = true;
        } else {
          try {
            route(at, one(tgt));
            done = true;
          } catch (PlannerError& e2) {
            if (e2.at < 0 && e2.reason.find("no route") != std::string::npos)
              again = true;
            else
              done = true;
          }
        }
      }
      if (done) break;
      if (again) continue;
    }
  }
}

void Planner::place_all(const SqSet& excluded) {
  switch (strategy) {
    case Strategy::Greedy: place_all_greedy(excluded); return;
    case Strategy::Edge: place_all_edge(excluded); return;
    case Strategy::Deps: place_all_deps(excluded); return;
    case Strategy::Peel: place_all_peel(excluded); return;
  }
}

void Planner::terminal_capture() {
  std::vector<int> royals;
  for (int q : pieces(0, K))
    if (target_for(q) < 0) royals.push_back(q);
  if (royals.size() != 1) throw err("expected one Black royal left, found " + std::to_string(royals.size()));
  int k = royals[0], s_r = terminal_sq;
  Piece piece = tat(s_r);
  std::vector<int> caps;
  for (int q : CANON)
    if (board[q] == piece && target.a[q] != piece) caps.push_back(q);
  std::vector<int> ts, ts2;
  if (caps.empty() && board[s_r] == piece) {
    single_moves([&](int t) { return board[t]; }, s_r, piece, ts);
    for (int t : ts) {
      if (board[t]) continue;
      Board b2 = board;
      b2[t] = b2[s_r];
      b2[s_r] = 0;
      single_moves([&](int q) { return b2[q]; }, t, b2[t], ts2);
      if (contains(ts2, s_r)) {
        do_(1, mv(s_r, t));
        caps = {t};
        break;
      }
    }
  }
  if (caps.empty()) throw err("terminal: capturer not found");
  int cap = caps[0];
  if (board[s_r] && s_r != k) displace(s_r, one(s_r), 0, two(cap, k));
  if (k != s_r) route(k, one(s_r), false, false, one(cap));
  SqSet origins;
  for (int a = 0; a < 144; ++a) {
    if (board[a] && a != cap) continue;
    Board probe = board;
    probe[cap] = 0;
    probe[a] = piece;
    single_moves([&](int q) { return probe[q]; }, a, piece, ts);
    if (contains(ts, s_r)) origins.set(a);
  }
  if (origins.none()) throw err("terminal: no origin square for the capturer");
  if (!origins[cap]) cap = route(cap, origins);
  place_all(one(s_r));
  auto reach = [&]() {
    if (!board[cap]) key_error(cap);
    single_moves([&](int q) { return board[q]; }, cap, board[cap], ts);
    return contains(ts, s_r);
  };
  if (board[s_r] != mk(0, K) || board[cap] != piece || !reach()) throw err("terminal: setup disturbed by re-placement");
  flush();
  fix_parity(1);
  if (!reach()) throw err("terminal: capture no longer possible");
  play(1, mv(cap, s_r));
}

void Planner::flush() {
  for (int k = 0; k < 10; ++k) {
    if (pending[0].empty() && pending[1].empty()) return;
    for (int side = 0; side < 2; ++side) {
      if (pending[side].empty()) continue;
      PMove m = pending[side].back();
      pending[side].pop_back();
      int a = m.from, b = m.to;
      if (board[b] || !board[a] || protected_[a]) continue;
      while (turn != side) wait(turn);
      if (!board[a]) key_error(a);
      Board nb = board;
      nb[b] = nb[a];
      nb[a] = 0;
      if (seen_after(nb, other(side))) {
        wait(side);
        pending[side].push_back(m);
        continue;
      }
      do_(side, m);
    }
  }
  throw err("could not flush waiting moves");
}

void Planner::fix_parity(int want) {
  if (turn == want) return;
  int side = turn;
  int lion = lion_sq(side);
  if (lion >= 0)
    for (int m : adjacent_empty(lion)) {
      PMove j = mv(lion, lion, false, m);
      if (eng.is_legal(j)) {
        play(side, j);
        return;
      }
    }
  std::vector<int> sqs;
  for (int sq : CANON)
    if (board[sq]) sqs.push_back(sq);
  std::vector<Piece> ps;
  for (int sq : sqs) ps.push_back(board[sq]);
  for (size_t i = 0; i < sqs.size(); ++i) {
    int sq = sqs[i];
    Piece p = ps[i];
    if (colour_of(p) != side || (role_of(p) != K && role_of(p) != Q)) continue;
    std::vector<int> emp = adjacent_empty(sq);
    for (int a : emp)
      for (int b : emp)
        if (cheb(a, b) == 1 && a != b) {
          play(side, mv(sq, a));
          wait(other(side));
          play(side, mv(a, b));
          flush();
          if (turn != side) wait(other(side));
          play(side, mv(b, sq));
          flush();
          return;
        }
  }
  throw err(std::string("cannot fix parity for ") + colour_ch(side));
}

void Planner::verify() {
  if (turn != end_turn || flag != -1)
    throw PlannerError{"verify", "ends with " + cstr(turn) + " to move, flag " + (flag < 0 ? "None" : rsq(flag)), -1};
  if (board != target.a) {
    std::vector<int> diff;
    for (int s = 0; s < 144; ++s)
      if (board[s] != target.a[s]) diff.push_back(s);
    std::string d = "[";
    for (size_t i = 0; i < diff.size() && i < 3; ++i)
      d += (i ? ", " : "") + ("(" + rsq(diff[i]) + ", " + rpiece(board[diff[i]]) + ", " + rpiece(target.a[diff[i]]) + ")");
    d += "]";
    throw PlannerError{"verify", "board differs on " + std::to_string(diff.size()) + " squares, e.g. " + d, -1};
  }
}

}  // namespace cp
