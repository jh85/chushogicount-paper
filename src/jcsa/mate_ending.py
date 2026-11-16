#!/usr/bin/env python3
"""How much would JCSA's checkmate ending change the count?  (docs/jcsa-rules-en.md U10)

Under the capture convention (D10) a game ends when a side's last royal is captured.
Under JCSA's checkmate ending it would end one ply earlier, when a side with a single
royal is mated (its royal attacked and every legal move leaves it capturable).  A
Black-to-move board T is then unreachable if every legal White last move comes from a
position P in which White was already mated.

Stage 1 (--share): uniform candidate boards (Black to move): share with
  (a) Black (to move) mated;              (what endings_share.py's 26 % measured)
  (b) White with a single royal, attacked, and mated if it were White's turn.
Stage 2 (--retract): for the (b) boards, complete one-ply retraction of White's last
move (single moves, un-captures of any Black piece, un-promotions incl. kirin/phoenix/
elephant, lion-type double moves with one or two un-captures, igui), every predecessor
P verified through the engine (the move is legal in P and reproduces T) and required to be
a candidate (I1–I10).  If no P has White un-mated, T is unreachable under the checkmate
ending.  Jitto predecessors (same board, White to move) are always mated when (b) holds.
Usage:
  python3 src/jcsa/mate_ending.py --share --n 200000 --seed 31 --procs 14 --out out/runs/mate_ending_seed31
  python3 src/jcsa/mate_ending.py --retract --procs 14 --out out/runs/mate_ending_seed31
"""
import argparse
import json
import math
import random
import sys
import time
from collections import Counter
from multiprocessing import Pool
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from count.sampler import to_sfen                                    # noqa: E402
from plan.moves import SQUARES, PROMOTES, cheb, single_moves, usi, usi_squares    # noqa: E402

_S = _E = _SETUP = None
BLACK_ROLES = sorted(set(PROMOTES) | set(PROMOTES.values()) | {"K", "N", "Q"})
UNPROMOTE = {}                                   # promoted/merged role -> base roles
for b, pr in PROMOTES.items():
    UNPROMOTE.setdefault(pr, []).append(b)
DOUBLE = {"N", "+H", "+D"}


def _init(sampler=True):
    global _S, _E, _SETUP
    from count.candidates import PRIMARY, chu_setup
    from count.sampler import Sampler
    from plan.engine import Engine
    if sampler:
        _S = Sampler(chu_setup("file", **PRIMARY), "file", True)
    _E = Engine()
    _SETUP = chu_setup("file", identify_royals=True, mover_royal_required=False)


def white_single_royal(board):
    return sum(1 for p in board.values() if p == ("W", "K")) == 1


def classify(board):
    """(black_mated, white_attacked, white_mated_if_turn) for a non-terminal board."""
    from jcsa.mode import mated, royal_capturable
    bm = mated(_E, board, "B", None)
    wa = white_single_royal(board) and royal_capturable(_E, board, "W")
    wm = wa and mated(_E, board, "W", None)
    return bm, wa, wm


def _candidate(P, cp=None):
    """I1-I10; with cp (CPlan) the I1-I9 test runs in chu-plan (`cand`, the same predicate,
    checked by tests/test_cmate.py --cand)."""
    from count.candidates import is_candidate
    from plan.lanes import lane_ok
    return (cp.cand(P) if cp else is_candidate(_SETUP, P, "file", True)) and lane_ok(P)


def predecessors(T, mover="W"):
    """Yield (P, usi move) for every geometrically possible last move of `mover` into T;
    the caller verifies with the engine.  Un-captured pieces are restricted to those that keep
    the captured side's free-piece groups (I6, I7, I9; candidates.py Group.ok) satisfied: in
    P that side's pieces are exactly T's plus the un-captured ones, so a violation there makes P
    a non-candidate (exact pre-filter of _candidate)."""
    from collections import Counter, defaultdict
    other = "B" if mover == "W" else "W"
    n0 = Counter(r for q, (c, r) in T.items() if c == other)
    w0 = defaultdict(list)
    for q, (c, r) in T.items():
        if c == other:
            w0[r].append(q)
    groups = _SETUP.free[other]
    memo = {}

    def cap_ok(*caps):                       # caps: (square, role) restored for `other`
        caps = tuple(x for x in caps if x[1])
        if not caps:
            return True
        if caps in memo:
            return memo[caps]
        n, w = Counter(n0), defaultdict(list, {r: list(v) for r, v in w0.items()})
        for q, r in caps:
            n[r] += 1
            w[r].append(q)
        ok = all(g.ok(lambda role: n[role], lambda role: w[role], True)
                 for g in groups if any(r in g.roles() for _, r in caps))
        memo[caps] = ok
        return ok
    empties = [q for q in SQUARES if q not in T]
    for s, (c, role) in list(T.items()):
        if c != mover:
            continue
        base = {q: p for q, p in T.items() if q != s}
        origin_roles = [(role, False)] + [(b, True) for b in UNPROMOTE.get(role, [])]
        for r0, promote in origin_roles:
            piece0 = (mover, r0)
            # single moves: origin a (empty in T) from which piece0 reaches s
            probe = dict(base)
            probe[s] = (other, "K")                             # capturable dummy on s
            for a in empties:
                probe[a] = piece0
                ok = s in single_moves(probe, a, piece0)
                del probe[a]
                if not ok:
                    continue
                for cap in [None] + BLACK_ROLES:
                    if not cap_ok((s, cap)):
                        continue
                    P = dict(base)
                    P[a] = piece0
                    if cap:
                        P[s] = (other, cap)
                    yield P, usi(a, s, promote=promote)
            # lion-type double moves (incl. igui a == s): a -> m -> s, m empty in T
            if r0 in DOUBLE:
                for m in empties:
                    if cheb(m, s) != 1:
                        continue
                    for a in [s] + [q for q in empties if cheb(q, m) == 1 and q != s]:
                        for cap_m in [None] + BLACK_ROLES:
                            if not cap_ok((m, cap_m)):
                                continue
                            for cap_s in ([None] if a == s else [None] + BLACK_ROLES):
                                if not cap_ok((m, cap_m), (s, cap_s)):
                                    continue
                                P = dict(base)
                                P[a] = piece0
                                if cap_m:
                                    P[m] = (other, cap_m)
                                if cap_s:
                                    P[s] = (other, cap_s)
                                yield P, usi(a, s, promote=promote, mid=m)


def legal_predecessors(T, mover="W", cp=None, key=None, max_key=None):
    """Yield (P, mv), each once: the predecessors(T, mover) that are candidates (I1-I10) and
    from which mv is legal and gives T (engine check).  key: if given, the raw predecessors are
    enumerated first and checked in the order of key(P, mv) (the same set, reordered); with
    max_key only those with key <= max_key (a subset)."""
    from count.sfen import parse
    seen = set()
    raw = predecessors(T, mover)
    if key is not None:
        raw = sorted(((key(*x), x) for x in raw), key=lambda kx: kx[0])
        raw = [x for k, x in raw if max_key is None or k <= max_key]
    for P, mv in raw:
        key = (frozenset(P.items()), mv)
        if key in seen:
            continue
        seen.add(key)
        if not _candidate(P, cp):
            continue
        sfen = to_sfen(P, mover.lower())
        _E.position(sfen)
        if mv not in _E.legal():
            continue
        _E.position(sfen, [mv])
        if parse(_E.sfen())[0] != T:
            continue
        yield P, mv


def retract(T, cp=None):
    """('reachable', P, mv) if some legal candidate predecessor has White un-mated;
    ('unreachable', n_pred) if every legal candidate predecessor has White mated;
    ('no-predecessor', 0) if none is legal.  With cp (plan/cplanner.py CPlan) the mate test
    is D13's: JCSA rules, no flag in P (the weakest case: a flag only removes White moves)."""
    from jcsa.mode import mated
    n_pred = 0
    for P, mv in legal_predecessors(T, "W", cp):
        n_pred += 1
        if not (cp.mated(P, "W", None, "jcsa") if cp else mated(_E, P, "W", None)):
            return "reachable", n_pred, mv
    return ("unreachable" if n_pred else "no-predecessor"), n_pred, None


def retract2(T, cp, max_q=20000):
    """Two-ply retraction under D13 (cp: chu-plan's JCSA mate test, no flag: the weakest
    case).  ('reachable', P, Q) for the first legal candidate P (White to move, not mated) with
    a legal candidate predecessor Q (Black to move, not mated); else ('unreachable', n_P, n_Q):
    every game into T passes through a mated position, so T is unreachable under D13;
    ('budget', n_p, n_q) after max_q predecessors Q without a decision.
    The candidate filter holds for either side to move here (both sides keep a royal)."""
    n_p = n_q = 0
    for P, mv in legal_predecessors(T, "W", cp):
        if cp.mated(P, "W", None, "jcsa"):
            continue
        n_p += 1
        for Q, mq in legal_predecessors(P, "B", cp):
            n_q += 1
            if n_q > max_q:
                return "budget", n_p, n_q
            if not cp.mated(Q, "B", None, "jcsa"):
                return "reachable", (P, mv), (Q, mq)
    return "unreachable", n_p, n_q


def _royal_first(P):
    """Order key for Black's retractions from P (docs/d13-planner.md F): when Black is caged in
    every P, Black's own last move made the attack, so retract Black's royal first, then Black
    pieces whose origin lies on a file, rank or diagonal through one of Black's royals (a blocker
    put back), then the rest."""
    royals = [q for q, p in P.items() if p == ("B", "K")]

    def key(Q, mq):
        a, s = usi_squares(mq)[0], usi_squares(mq)[-1]
        if P.get(s) == ("B", "K"):
            return 0
        for r in royals:
            dx, dy = a[0] - r[0], a[1] - r[1]
            if dx == 0 or dy == 0 or abs(dx) == abs(dy):
                return 1
        return 2
    return key


def chains2(T, cp, max_q=20000, k=8, royal_first=False, royal_only=False):
    """Up to k two-ply chains ((P, mv), (Q, mq)) as retract2 finds them (P White to move and not
    mated, Q Black to move and not mated), at most one per P; the search of retract2 with the same
    budget.  royal_first: Black's retractions in the order of _royal_first; royal_only: only its
    first two classes (royal retractions and blockers put back).  For the q2 route of
    pipeline "v2" (docs/d13-planner.md F)."""
    out, n_q = [], 0
    for P, mv in legal_predecessors(T, "W", cp):
        if cp.mated(P, "W", None, "jcsa"):
            continue
        rk = _royal_first(P) if royal_first or royal_only else None
        for Q, mq in legal_predecessors(P, "B", cp, key=rk, max_key=1 if royal_only else None):
            n_q += 1
            if n_q > max_q:
                return out
            if not cp.mated(Q, "B", None, "jcsa"):
                out.append(((P, mv), (Q, mq)))
                break
        if len(out) >= k:
            break
    return out


def _share_work(args):
    seed, n = args
    rng = random.Random(seed)
    c = Counter()
    keep = []
    for _ in range(n):
        board = _S.sample(rng)[0]
        if not any(p == ("B", "K") for p in board.values()):
            c["terminal (skipped)"] += 1
            continue
        c["boards"] += 1
        bm, wa, wm = classify(board)
        c["black mated"] += bm
        c["white single royal attacked"] += wa
        c["white mated if White's turn"] += wm
        if wm:
            keep.append(to_sfen(board, "b"))
    return c, keep


def _retract_work(sfen):
    from count.sfen import parse
    T = parse(sfen)[0]
    t0 = time.time()
    verdict, n_pred, mv = retract(T)
    return {"sfen": sfen, "verdict": verdict, "predecessors_checked": n_pred, "unmated_predecessor_move": mv, "secs": round(time.time() - t0, 1)}


def cp_interval(c, n, level=0.9973):
    from plan.estimate import clopper_pearson
    return clopper_pearson(c, n, level)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--share", action="store_true")
    ap.add_argument("--retract", action="store_true")
    ap.add_argument("--n", type=int, default=10000)
    ap.add_argument("--seed", type=int, default=31)
    ap.add_argument("--procs", type=int, default=14)
    ap.add_argument("--out", required=True, help="prefix for <out>_boards.jsonl / <out>_retract.jsonl")
    ap.add_argument("--limit", type=int, default=0, help="retract: at most this many boards")
    a = ap.parse_args()
    t0 = time.time()
    if a.share:
        chunks = max(a.procs * 4, a.n // 2000)
        per = a.n // chunks
        tot = Counter()
        kept = []
        with Pool(a.procs, initializer=_init) as pool:
            for i, (c, keep) in enumerate(pool.imap_unordered(_share_work, [(a.seed * 7001 + i, per) for i in range(chunks)])):
                tot.update(c)
                kept += keep
                if (i + 1) % 20 == 0:
                    print(f"  ... {tot['boards']} boards, white-mated {tot[chr(119) + 'hite mated if White' + chr(39) + 's turn']}", flush=True)
        n = tot["boards"]
        with open(f"{a.out}_boards.jsonl", "w") as fh:
            fh.write(json.dumps({"header": True, "seed": a.seed, "sampled_nonterminal": n, "counts": dict(tot)}) + "\n")
            for s in kept:
                fh.write(json.dumps({"sfen": s}) + "\n")
        print(f"non-terminal candidate boards: {n} (seed {a.seed}); {time.time() - t0:.0f}s")
        for k, v in sorted(tot.items()):
            lo, hi = cp_interval(v, n)
            print(f"  {k}: {v}  share {v / n:.4e}  [{lo:.3e}, {hi:.3e}] (Clopper-Pearson 99.73 %)")
    if a.retract:
        rows = [json.loads(l) for l in open(f"{a.out}_boards.jsonl")]
        header, boards = rows[0], [r["sfen"] for r in rows[1:]]
        if a.limit:
            boards = boards[:a.limit]
        n = header["sampled_nonterminal"]
        res = Counter()
        with Pool(a.procs, initializer=_init) as pool, open(f"{a.out}_retract.jsonl", "w") as fh:
            for i, r in enumerate(pool.imap_unordered(_retract_work, boards)):
                res[r["verdict"]] += 1
                fh.write(json.dumps(r) + "\n")
                fh.flush()
                if (i + 1) % 100 == 0:
                    print(f"  ... {i + 1}/{len(boards)} {dict(res)} {time.time() - t0:.0f}s", flush=True)
        u = res["unreachable"] + res["no-predecessor"]
        print(f"retraction on {len(boards)} boards with White mated-if-turn (of {n} sampled non-terminal boards, seed {header['seed']}): {dict(res)}; {time.time() - t0:.0f}s")
        if a.limit and len(boards) < len(rows) - 1:
            print("  (limited subset: shares below use the subset's fraction of the (b) boards)")
            frac = u / len(boards)
            b_total = len(rows) - 1
            lo, hi = cp_interval(u, len(boards))
            print(f"  unreachable share among (b) boards {frac:.4f} [{lo:.4f}, {hi:.4f}]; times (b) share {b_total / n:.4e} -> {frac * b_total / n:.3e} of all boards (point)")
        else:
            lo, hi = cp_interval(u, n)
            print(f"  unreachable under the checkmate ending: {u} of {n} boards = {u / n:.4e}  [{lo:.3e}, {hi:.3e}] (Clopper-Pearson 99.73 %) — lower bound on the ending's effect")


if __name__ == "__main__":
    main()
