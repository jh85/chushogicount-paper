"""Mate-avoiding proof games for the literal JCSA checkmate ending (decision D13; pilot).

Under D13 a position in which the side to move is mated (one royal, attacked, every legal
move leaves a royal capturable; JCSA move rules) is terminal.  A proof game for a target T
may therefore pass through no mated position except, when T itself is mated, the last.

MatePlanner is plan/planner.py's Planner with one more rule on every move: it must not
leave the opponent mated, and must not leave the mover in a self-made cage (mated if it
were to move: any reply but a block would mate it), unless the resulting state is the final
target (safe()).  When a planned move mv of side S breaks the rule, the planner makes room
for it: two moves are inserted before mv, either (a tempo of S, a safety move of O) or (a
safety move of S, a tempo of O), found by lookahead so that every state on the way is safe
and mv is legal and safe after them.  Inserted moves are single non-capturing steps or
jitto: pieces not yet on their target square first (no return needed: placement routes
them anyway), then reversible pieces on their target square (returned later through the
planner's pending returns, like its waiting moves, under the same rule), royals last.
The pair search runs in chu-plan (fixpair: every state after a, b and mv safe, without the
final-target exception, which can only refuse a pair); Python then plays the first pair
whose states are not repetitions.  fast=False runs the same search in Python, with lookahead
on the engine (restoring its exact SFEN).
The mate test is chu-plan's (src/plan/cpp/mate.cpp, checked against jcsa/mode.py mated()).

Games are untrusted: certify_d13() checks the game with plan/certify.py and replays it
under JCSA move rules (chu-plan `mates`), which also lists every mated position.
Planner (and so chu-plan) is unchanged; this module is the Python prototype for the pilot.
"""
import sys
from pathlib import Path

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from count.sfen import parse                                        # noqa: E402
from plan.moves import SQUARES, cheb, single_moves, usi, usi_squares  # noqa: E402
from plan.planner import MAX_PLIES, OTHER, REVERSIBLE, Planner, PlannerError, Repetition  # noqa: E402

MAX_FIXES = 600             # room-making episodes per game
_EDGE = dict(strategy="edge", defer=True)
# (planner seed, Planner strategy keywords): estimate.py's cascade order (baseline seeds, edge-first
# with deferral, dependency-aware with and without parking); pipeline "v2" (docs/d13-planner.md E)
_DEPS = dict(strategy="deps", defer=True, park=True)
_HAVEN = dict(haven=True)
STRATEGIES = tuple((s, {}) for s in range(6)) + ((101, _EDGE), (102, _EDGE),
              (0, _DEPS), (1, dict(strategy="deps", defer=True, park=False)),
              (0, _HAVEN), (1, _HAVEN), (0, dict(_HAVEN, shield=True)), (0, dict(_DEPS, haven=True)))
PRED_STRATEGIES = STRATEGIES[:2] + STRATEGIES[6:7] + STRATEGIES[8:10] + STRATEGIES[10:11] + STRATEGIES[13:]
# relax_d13 stages of pipeline "v2": P2's call first (so v2 repeats every P2 attempt), then deeper
RELAX_STAGES = ({}, dict(depth=6, beam=16, tries=12), dict(depth=16, beam=24, tries=16),
                dict(depth=32, beam=48, tries=16))


class MatePlanner(Planner):
    def __init__(self, target, engine=None, cp=None, fast=True, shield=False, haven=False, **kw):
        from plan.cplanner import CPlan
        self.cp = cp or CPlan()
        self.fast = fast
        self.shield = shield
        self.haven = haven
        self._haven_side = None     # set while a royal of this side is being displaced
        self._raw = False           # inside a fix: moves are checked by the fix itself
        self.fixes = 0
        super().__init__(target, engine, **kw)

    def before_files(self, tcount):
        """Second-royal shield (docs/d13-planner.md A): a side whose target keeps two royals (king
        and crown prince) promotes its drunk elephant now instead of in phase C, so that from here
        on it has two royals and cannot be mated (D13)."""
        if self.shield:
            self.phase = "S-shield"
            for side in "BW":
                if tcount[(side, "K")] == 2 and self.pieces(side, "E"):
                    self.into_zone(self.pieces(side, "E")[0])
                    self.early.add((side, "E"))
        if self.haven:
            self.phase = "S-haven"
            for side in "BW":
                if (side, "E") in self.early:
                    continue                # two royals: cannot be mated
                for sq in self.pieces(side, "K"):
                    if sum(t not in self.board for t in self.adjacent_empty(sq)) >= 2:
                        continue
                    goals = [t for t in self.empty_squares() if self.haven_ok(t, side, sq)]
                    goals.sort(key=lambda t: cheb(t, sq))
                    if goals:
                        try:
                            self.route(sq, set(goals[:12]))
                        except PlannerError:
                            pass            # stays boxed in; the room-making fixes remain

    # --- royal havens (docs/d13-planner.md B) -----------------------------------
    def haven_ok(self, t, side, frm=None):
        """t is a haven for a royal of side (coming from frm): outside the enemy camp, at least
        three empty neighbours, no enemy piece within two squares."""
        if (t[1] >= 9) if side == "B" else (t[1] <= 4):
            return False
        empty = sum(1 for q in SQUARES if cheb(q, t) == 1 and (q not in self.board or q == frm))
        if empty < 3:
            return False
        return not any(c != side and cheb(q, t) <= 2 for q, (c, _) in self.board.items())

    def empty_squares(self):
        out = super().empty_squares()
        if self._haven_side:
            good = [t for t in out if self.haven_ok(t, self._haven_side)]
            return good or out
        return out

    def displace(self, sq, avoid, *a, **kw):
        """Planner.displace; with haven, a royal is displaced only to havens (if there are any)."""
        prev = self._haven_side
        piece = self.board.get(sq)
        self._haven_side = piece[0] if self.haven and piece and piece[1] == "K" else None
        try:
            return super().displace(sq, avoid, *a, **kw)
        finally:
            self._haven_side = prev

    # --- engine state -------------------------------------------------------
    def sync(self):
        self.sfen_now = self.eng.sfen()
        self.board, self.turn, self.flag = parse(self.sfen_now)

    def restore(self, sfen):
        self.eng.position(sfen)
        self.sync()

    def final_ok(self):
        return self.turn == self.end_turn and self.flag == self.flag_target and self.board == self.target

    def side_to_move_mated(self):
        return self.mated_if_turn(self.turn, self.flag)

    def mated_if_turn(self, side, flag=None):
        return self.cp.mated(self.board, side, flag)

    def safe(self):
        """The state after a move is acceptable: it is the final target, or the side to move
        is not mated and the side that just moved would not be mated if it were to move
        (otherwise every reply but a block would mate it)."""
        if self.final_ok():
            return True
        return not self.side_to_move_mated() and not self.mated_if_turn(OTHER[self.turn])

    def _push(self, mv):
        """Raw move for lookahead and fixes: (ok, previous sfen); refuses illegal moves and
        repeated states.  The caller pops or keeps it."""
        if mv not in self.eng.legal():
            return False, None
        prev = self.sfen_now
        self.eng.move(mv)
        self.moves.append(mv)
        self.sync()
        st = self.state()
        if st in self.seen:                 # a real earlier state: undo, keep it in seen
            self.moves.pop()
            self.restore(prev)
            return False, None
        self.seen.add(st)
        return True, prev

    def _pop(self, prev):
        self.seen.discard(self.state())
        self.moves.pop()
        self.restore(prev)

    def _keep(self):
        if len(self.moves) > MAX_PLIES:
            raise PlannerError(self.phase, "too many plies")

    # --- the rule -----------------------------------------------------------
    def play(self, side, mv, _retry=3):
        """Planner.play plus the D13 rule (the code above the check is Planner.play's)."""
        assert self.turn == side, (self.turn, side, mv)
        if _retry and self.would_repeat(mv):
            self.perturb(side, usi_squares(mv)[0])
            while self.turn != side:
                self.wait(self.turn)
            if usi_squares(mv)[1] in self.board:
                raise PlannerError(self.phase, f"destination of {mv} taken while avoiding repetition")
            return self.play(side, mv, _retry=_retry - 1)
        if mv not in self.eng.legal():
            raise PlannerError(self.phase, f"illegal move {mv} for {side}")
        prev = self.sfen_now
        self.eng.move(mv)
        self.moves.append(mv)
        if len(self.moves) > MAX_PLIES:
            raise PlannerError(self.phase, "too many plies")
        self.sync()
        st = self.state()
        if st in self.seen:
            raise Repetition(f"{self.phase}: repetition after {mv}")
        if not self._raw and not self.safe():
            self.moves.pop()
            self.restore(prev)
            return self._fix(side, mv)
        self.seen.add(st)

    def _steps(self, side, near=None):
        """Single non-capturing steps of `side` as (move, return or None): first pieces not on
        their target square (no return needed: placement routes them anyway), then reversible
        pieces on their target square (returned later), royals last; each group by distance
        to `near`.  Jitto first if the side has a lion.  No reserved or protected squares."""
        out = []
        lion = self.lion_sq(side)
        if lion:
            out += [((-1, 0), usi(lion, lion, mid=m), None) for m in self.adjacent_empty(lion)]
        for sq, (c, role) in self.board.items():
            if c != side or sq in self.reserved or sq in self.protected:
                continue
            placed = self.target.get(sq) == (c, role)
            if placed and role not in REVERSIBLE:
                continue
            if not placed and role in ("P", "L"):
                continue                    # walls never move backwards: no free steps
            for t in single_moves(self.board, sq):
                if t in self.board or t in self.reserved:
                    continue
                group = 2 if role == "K" else (1 if placed else 0)
                back = usi(t, sq) if placed and role in REVERSIBLE else None
                out.append(((group, cheb(sq, near) if near else 0), usi(sq, t), back))
        out.sort(key=lambda x: x[0])
        return [(m, r) for _, m, r in out]

    def _fix(self, side, mv):
        """Insert two moves before mv, either (a tempo of side, a safety move of o) or (a
        safety move of side, a tempo of o), every resulting state safe(), mv legal and safe
        after them."""
        self.fixes += 1
        if self.fixes > MAX_FIXES:
            raise PlannerError("mate", "too many fixes")
        o = OTHER[side]
        sroyal = next((q for q, p in self.board.items() if p == (side, "K")), None)
        oroyal = next((q for q, p in self.board.items() if p == (o, "K")), None)
        self._raw = True
        try:
            done = self._fix_fast(side, mv, sroyal, oroyal) if self.fast else False
            for a, back_a in ([] if self.fast else self._steps(side, near=sroyal)[:40]):
                ok, pa = self._push(a)
                if not ok:
                    continue
                if not self.safe():
                    self._pop(pa)
                    continue
                for b, back_b in self._steps(o, near=oroyal)[:40]:
                    ok, pb = self._push(b)
                    if not ok:
                        continue
                    if not self.safe():
                        self._pop(pb)
                        continue
                    ok, pm = self._push(mv)
                    if ok:
                        good = self.safe()
                        self._pop(pm)
                        if good:
                            for side_, back in ((side, back_a), (o, back_b)):
                                if back:
                                    self.pending[side_].append(back)
                            done = True
                            break
                    self._pop(pb)
                if done:
                    break
                self._pop(pa)
            if not done:
                raise PlannerError("mate", f"no room for {side} {mv}")
            self._keep()
        finally:
            self._raw = False
        self.play(side, mv)

    def _fix_fast(self, side, mv, sroyal, oroyal):
        """_fix's search in chu-plan; plays a and b of the first pair without repetitions."""
        o = OTHER[side]
        sa = []
        for a, back in self._steps(side, near=sroyal)[:40]:
            ok, pa = self._push(a)          # the Python search skips a repeated or illegal a
            if ok:
                self._pop(pa)
                sa.append((a, back))
        board, sb = self.board, []
        for a, _ in sa:                     # o's steps on the board after a, as the Python search
            q = usi_squares(a)
            f, t = q[0], q[-1]
            self.board = dict(board)
            if f != t:
                self.board[t] = self.board.pop(f)
            sb.append(self._steps(o, near=oroyal)[:40])
        self.board = board
        for k in (16, 256, 1 << 20):
            pairs = self.cp.fixpairs(self.board, self.turn, self.flag, mv, [m for m, _ in sa],
                                     [[m for m, _ in b] for b in sb], k)
            for i, j in pairs:
                ok, pa = self._push(sa[i][0])
                if not ok:
                    continue
                ok, pb = self._push(sb[i][j][0])
                if not ok:
                    self._pop(pa)
                    continue
                ok, pm = self._push(mv)
                if not ok:
                    self._pop(pb)
                    self._pop(pa)
                    continue
                self._pop(pm)
                for side_, back in ((side, sa[i][1]), (o, sb[i][j][1])):
                    if back:
                        self.pending[side_].append(back)
                return True
            if len(pairs) < k:
                return False
        return False


def certify_d13(moves, target, cp, engine=None, turn="B", flag=None):
    """(ok, why): plan/certify.py's checks, plus a replay under JCSA move rules in which the
    side to move is mated in no position but the last, and in the last iff the target is."""
    from plan.certify import certify
    ok, why = certify(moves, target, engine=engine, turn=turn, flag=flag)
    if not ok:
        return False, why
    try:
        mates = cp.mates(moves)
    except ValueError as e:
        return False, f"JCSA-illegal move at ply {e.args[0]}"
    want_last = cp.mated(target, turn, flag)
    early = [k for k in mates if k < len(moves)]
    if early:
        return False, f"{len(early)} mated positions before the end, first at ply {early[0]}"
    if (len(moves) in mates) != want_last:
        return False, f"final position mated {len(moves) in mates}, target mated {want_last}"
    return True, "ok"


def classify_d13(T, cp):
    """(black mated, white caged): the side to move (Black) mated in T; White would be mated
    in T if it were to move (then White's last move must have made the cage)."""
    return cp.mated(T, "B"), cp.mated(T, "W")


def last_moves(T, cp, eng, limit=8, extra=4):
    """Candidate White last moves into T for the predecessor route, White not mated in P (D13
    test, no flag): first up to `limit` non-capturing, non-promoting retractions (plan/relax.py
    predecessors), then up to `extra` others from the complete one-ply retraction of
    jcsa/mate_ending.py (captures, promotions, double moves; P a candidate, mv legal and
    giving T); each group by plan/relax.py pocket score."""
    from jcsa import mate_ending
    from plan.relax import pocket_score, predecessors
    first = sorted(((pocket_score(P), P, mv) for P, mv in predecessors(T, "B", eng)
                    if not cp.mated(P, "W")), key=lambda x: x[0])[:limit]
    tried = {(frozenset(P.items()), mv) for _, P, mv in first}
    if mate_ending._E is None:
        mate_ending._init(sampler=False)
    rest = sorted(((pocket_score(P), P, mv) for P, mv in mate_ending.legal_predecessors(T, "W", cp)
                   if (frozenset(P.items()), mv) not in tried and not cp.mated(P, "W", None, "jcsa")),
                  key=lambda x: x[0])[:extra]
    return [(P, mv) for _, P, mv in first + rest]


def relax_d13(T, cp, eng, turn="B", depth=6, beam=16, tries=12, per_level=3, seeds=(0, 1), log=None,
              kws=None, full_levels=0):
    """Retro-relaxation under D13: beam search backward from T (side `turn` to move) with
    plan/relax.py predecessors (non-capturing, non-promoting retractions, colours alternating,
    candidate, forward move legal), dropping every position whose side to move is mated
    (terminal under D13).  Plain positions (neither side mated or caged) are planned with
    MatePlanner, best first (fewest plies retracted, then pocket score), at most `per_level`
    bases per level and `tries` in all; the retracted moves are appended and the game is checked
    with certify_d13.  At the first level of a Black-to-move T the complete one-ply retraction
    (jcsa/mate_ending.py: captures, promotions, double moves) is added; with full_levels = k > 0
    instead at the first k levels, for either side.  kws: the planner attempts per base as
    (seed, Planner keywords), default one per seed without keywords.
    Returns (moves, info) or (None, info)."""
    import hashlib
    from plan.relax import pocket_score, predecessors

    def digest(b, t):
        return hashlib.blake2b((t + repr(sorted(b.items()))).encode(), digest_size=16).digest()

    level = [(T, turn, [])]
    seen = {digest(T, turn)}
    tried = 0
    info = {"levels": 0, "tried": 0, "why": "no plain predecessor"}
    for d in range(1, depth + 1):
        nxt = []
        for X, t, fwd in level:
            pt = OTHER[t]                                   # side to move in the predecessor
            gen = predecessors(X, t, eng)
            if (d <= full_levels) if full_levels else (d == 1 and t == "B"):
                from itertools import chain
                from jcsa import mate_ending
                if mate_ending._E is None:
                    mate_ending._init(sampler=False)
                gen = chain(gen, mate_ending.legal_predecessors(X, OTHER[t], cp))
            for P, mv in gen:
                key = digest(P, pt)
                if key in seen:
                    continue
                seen.add(key)
                if cp.mated(P, pt):
                    continue
                plain = not cp.mated(P, t)
                nxt.append((not plain, pocket_score(P), P, pt, [mv] + fwd))
        info["levels"] = d
        if not nxt:
            break
        nxt.sort(key=lambda x: (x[0], x[1]))
        here = 0
        for caged, _, P, pt, fwd in nxt:
            if caged or tried >= tries or here >= per_level:
                break
            tried += 1
            here += 1
            for s, kw in (kws or [(s, {}) for s in seeds]):
                p = MatePlanner(P, eng, cp=cp, seed=s, end_turn=pt, **kw)
                try:
                    moves = p.run()
                except (PlannerError, Repetition) as e:
                    info["why"] = str(e)[:80]
                    continue
                except Exception as e:                      # the planner's own bookkeeping errors
                    info["why"] = f"EXCEPTION {type(e).__name__}: {e}"[:80]
                    continue
                game = moves + fwd
                ok, why = certify_d13(game, T, cp, engine=eng, turn=turn)
                if ok:
                    info.update(tried=tried, retracted=len(fwd), seed=s, fixes=p.fixes)
                    return game, info
                info["why"] = f"CERTIFY {why}"[:80]
        if tried >= tries:
            break
        level = [(P, pt, fwd) for _, _, P, pt, fwd in nxt[:beam]]
    info["tried"] = tried
    return None, info


def plan_d13(T, cp, eng, seeds=range(6), preds=8, extra=4, relax=True, pipeline="p2"):
    """A D13 certificate for the non-terminal Black-to-move target T: {"ok": True, "moves",
    "route": "direct" | "pred" | "relax", "seed", "fixes"} or {"ok": False, "reason"}.  Plain
    targets (Black not mated, White not caged) are planned directly first; otherwise, and as a
    fallback, through a predecessor P (White to move, White not mated) and White's last move
    (last_moves: the complete retraction), then by relax_d13.
    pipeline "p2": pilot P2's attempt list.  "v2" (docs/d13-planner.md, step 1) adds the cascade
    strategies and the royal haven / second-royal shield (STRATEGIES) to the direct route, a
    second predecessor pass over 12 + 12 last moves with PRED_STRATEGIES, and relax_d13 in the
    stages RELAX_STAGES (after P2's own call) with PRED_STRATEGIES and the complete retraction
    at the first three levels.  Every attempt of "p2" is made by "v2" too, in the same order
    within each route."""
    bm, wc = classify_d13(T, cp)
    last = "none"
    v2 = pipeline == "v2"

    def attempt(target, end_turn, s, kw=None):
        nonlocal last
        p = MatePlanner(target, eng, cp=cp, seed=s, end_turn=end_turn, **(kw or {}))
        try:
            return p.run(), p.fixes
        except (PlannerError, Repetition) as e:
            last = str(e)[:80]
        except Exception as e:                      # the planner's own bookkeeping errors
            last = f"EXCEPTION {type(e).__name__}: {e}"[:80]
        return None, p.fixes

    if not bm and not wc:
        for s, kw in (STRATEGIES if v2 else [(s, {}) for s in seeds]):
            moves, fixes = attempt(T, "B", s, kw)
            if moves:
                ok, why = certify_d13(moves, T, cp, engine=eng)
                if ok:
                    return {"ok": True, "moves": moves, "route": "direct", "seed": s, "fixes": fixes,
                            "strategy": kw.get("strategy", "base")}
                last = f"CERTIFY {why}"[:80]
    passes = [((preds, extra), [(s, {}) for s in seeds[:2]])]
    if v2:
        passes.append(((12, 12), PRED_STRATEGIES[2:]))
    for (lim, ext), kws in passes:
        for P, mv in last_moves(T, cp, eng, limit=lim, extra=ext):
            for s, kw in kws:
                moves, fixes = attempt(P, "W", s, kw)
                if moves:
                    game = moves + [mv]
                    ok, why = certify_d13(game, T, cp, engine=eng)
                    if ok:
                        return {"ok": True, "moves": game, "route": "pred", "seed": s, "fixes": fixes,
                                "strategy": kw.get("strategy", "base")}
                    last = f"CERTIFY {why}"[:80]
    if relax:
        for kw in (RELAX_STAGES if v2 else [{}]):
            extra_kw = dict(kws=PRED_STRATEGIES, full_levels=3, per_level=4) if kw else {}
            moves, info = relax_d13(T, cp, eng, **kw, **extra_kw)
            if moves:
                return {"ok": True, "moves": moves, "route": "relax", "seed": info["seed"], "fixes": info["fixes"],
                        "retracted": info["retracted"], "relax_depth": kw.get("depth", 6)}
            last = f"relax: {info['why']}"[:80]
    return {"ok": False, "reason": last, "black_mated": bm, "white_caged": wc}
