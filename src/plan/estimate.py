#!/usr/bin/env python3
"""Stratified estimator with oversampling of the rare strata (Eii, session 3).

Strata and estimands (Black to move):
  nonterm : boards with a Black royal,            |C_nt| * p1
  flags   : effective-flag states of such boards, |C_nt| * E[k] * p2
            (E[k] = mean number of effective-flag states per non-terminal board,
             from the 10^8 static run of flags.py; (board, flag) pairs are sampled
             uniformly by accepting a board with probability k/3 and picking one flag
             uniformly, which needs k <= 3: a side has at most two lions)
  term    : boards with no Black royal,           |C_t| * p3
p = fraction reachable.  The registered statement (registered_brackets, runs.md M-D/M-E):
exact one-sided Clopper-Pearson lower bounds on p1 p2 p3 and normal bounds on E[k] and the
two I10 shares, Bonferroni over six components at alpha = 0.00135/6 each; I10 samples are
excluded from the denominators, unresolved samples count as unreachable; the upper end is
the cap |C_nt|(1 - s_nt)(1 + E[k]) + |C_t|(1 - s_t) (point estimates).  summarize() also
prints per-stratum two-sided 99.73 % Clopper-Pearson intervals, for information only.
The supplementary strict bracket is computed by strict_bracket.py.

Certificates: flag-off boards by the planner (+ retro-relaxation); flag states and
terminal boards through a predecessor P (the capturer on an origin square, the
captured lion / royal on the flag / capture square, White to move): planner game to
P (+ relaxation of P), then the capture, certified against the target with the
flag (certify.py).

Usage: python3 src/plan/estimate.py --seed S --nonterm 3000 --flags 300 --term 150 --procs 8
Writes out/runs/<tag>.jsonl and a summary; fixed sizes, no early stopping.
"""
import argparse
import json
import math
import random
import sys
import time
from multiprocessing import Pool
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from count.candidates import chu_setup, count, is_candidate      # noqa: E402
from count.sampler import Sampler, to_sfen                        # noqa: E402

# static effective-flag share of non-terminal boards, flags.py --jcsa --n 100000000 --seed 171
# (out/runs/flags_jcsa_1e8_seed171.log, lishogi marginal; run M-E step 1)
FLAG_COUNTS = {0: 96922420, 1: 1746711, 2: 271066, 3: 35113}
_n = sum(FLAG_COUNTS.values())
EK = sum(k * v for k, v in FLAG_COUNTS.items()) / _n
EK_SE = math.sqrt((sum(k * k * v for k, v in FLAG_COUNTS.items()) / _n - EK ** 2) / _n)
KMAX = 3
# I10 violation share per stratum (src/plan/lanes.py --n 10000000 --seed 173, out/runs/lanes_1e7_seed173.log; M-E step 2): proven unreachable
I10_SHARE = {"nonterm": (0.00119, 0.00001), "term": (0.00120, 0.00001)}   # (share, 1σ)
# JCSA effective-flag states per non-terminal board, paired with E[k] on the same boards
# (src/plan/flags.py --jcsa --seed 171, out/runs/flags_jcsa_1e8_seed171.log; M-E step 1)
EK_JCSA, EK_JCSA_SE = 0.01922, 0.0000138
JCSA = False                      # --jcsa: replay every certificate under JCSA, sample the JCSA flag stratum
PLANNER = "python"                # --planner cpp: plan/cplanner.py (chu-plan), the same games faster
CASCADE = ()                      # --cascade A,B,C,D: follow-up relaxation stages (followup.STAGE_PARAMS) appended
FIX_TURN = False                  # --fix-relax-turn: relax() certifies even retraction depths too (relax.py)
NCOMP = 6                         # Bonferroni components of the registered bracket
ALPHA = 0.00135 / NCOMP

_ctx = {}


def clopper_pearson(c, n, level=0.9973):
    """Exact two-sided binomial bounds for c successes in n trials."""
    if n == 0:
        return 0.0, 1.0
    alpha = 1 - level

    def cdf(p, k):                      # P(X <= k)
        if p <= 0:
            return 1.0
        if p >= 1:
            return 0.0
        tot = 0.0
        for i in range(k + 1):
            tot += math.exp(math.lgamma(n + 1) - math.lgamma(i + 1) - math.lgamma(n - i + 1)
                            + i * math.log(p) + (n - i) * math.log(1 - p))
        return tot

    def solve(f, lo, hi):
        for _ in range(60):
            mid = (lo + hi) / 2
            if f(mid):
                lo = mid
            else:
                hi = mid
        return lo
    lower = 0.0 if c == 0 else solve(lambda p: 1 - cdf(p, c - 1) < alpha / 2, 0.0, 1.0)
    upper = 1.0 if c == n else solve(lambda p: cdf(p, c) > alpha / 2, 0.0, 1.0)
    return lower, upper


def _init(jcsa=False, planner="python", cascade=(), fix_turn=False):
    global JCSA, PLANNER, CASCADE, FIX_TURN
    from plan.engine import Engine
    PLANNER, CASCADE, FIX_TURN = planner, tuple(cascade), fix_turn
    if planner == "cpp":
        from plan.cplanner import CPlan
        _ctx["cp"] = CPlan()
    _ctx["nonterm"] = Sampler(chu_setup("file", identify_royals=True), "file", True)
    _ctx["term"] = Sampler(chu_setup("file", identify_royals=True, terminal_only=True), "file", True)
    _ctx["engine"] = Engine()
    _ctx["setup"] = chu_setup("file", identify_royals=True)
    JCSA = jcsa
    if jcsa:
        _ctx["replay"], _ctx["jeng"] = Engine(), Engine()


def _jcsa_check(res, moves):
    """Attach the JCSA replay verdict of a lishogi certificate to its result."""
    if JCSA and res.get("ok"):
        from jcsa.mode import replay_jcsa
        ok, ply, mv, cat, _ = replay_jcsa(moves, _ctx["replay"], _ctx["jeng"])
        res["jcsa_ok"] = ok
        if not ok:
            res["jcsa_fail"] = {"ply": ply, "move": mv, "category": cat}
    return res


def _plan(T, retries, turn="B", tail=(), target=None, flag=None, use_relax=True):
    """Baseline: `retries` planner seeds (greedy / peeling by parity) then
    relaxation (depth 10, beam 12).  Fallbacks, additive: edge-first insertion
    with deferral (2 seeds), then deep relaxation (depth 16, beam 24), then the
    stages in CASCADE (--cascade).  The result records which stage produced the
    certificate.  PLANNER selects the Python planner or chu-plan (same games)."""
    from plan.certify import certify
    from plan.planner import Planner, PlannerError, Repetition
    from plan.relax import relax
    target = T if target is None else target
    eng = _ctx["engine"]
    last = None

    def attempt(seed, strategy=None, defer=False, stage="baseline", park=False):
        nonlocal last
        try:
            if PLANNER == "cpp":
                moves = _ctx["cp"].plan(T, seed=seed, end_turn=turn, strategy=strategy, defer=defer, park=park)
            else:
                moves = Planner(T, eng, seed=seed, end_turn=turn, strategy=strategy, defer=defer, park=park).run()
        except (PlannerError, Repetition) as e:
            last = str(e)[:80]
            return None
        except Exception as e:
            last = f"EXCEPTION {getattr(e, 'typ', type(e).__name__)}: {e}"[:80]
            return None
        ok, why = certify(moves + list(tail), target, flag=flag, engine=eng)
        if ok:
            return _jcsa_check({"ok": True, "plies": len(moves) + len(tail), "attempt": seed, "stage": stage}, moves + list(tail))
        last = f"CERTIFY {why}"
        return None

    def relaxed(depth, beam, tries, stage, planner_retries=2):
        nonlocal last
        if PLANNER == "cpp":
            moves, info = _ctx["cp"].relax(T, depth=depth, beam=beam, tries=tries,
                                           planner_retries=planner_retries, turn=turn, fix_turn=FIX_TURN)
        else:
            moves, info = relax(T, eng, depth=depth, beam=beam, tries=tries, planner_retries=planner_retries,
                                turn=turn, compact_seen=bool(CASCADE), fix_turn=FIX_TURN)
        if moves:
            ok, why = certify(moves + list(tail), target, flag=flag, engine=eng)
            if ok:
                return _jcsa_check({"ok": True, "plies": len(moves) + len(tail), "rescued": info["retracted"], "stage": stage}, moves + list(tail))
            last = f"CERTIFY after relax {why}"
        else:
            last = f"{last} | relax {info['tried']}/{info['levels']}"
        return None

    for seed in range(retries):
        r = attempt(seed)
        if r:
            return r
    if not use_relax:
        return {"ok": False, "reason": last}
    r = relaxed(10, 12, 4, "relax")
    if r:
        return r
    for seed in (101, 102):                                   # fallback 1: edge-first + deferral
        r = attempt(seed, strategy="edge", defer=True, stage="edge")
        if r:
            return r
    # fallback 1b (2026-10-06, after run M-B was registered; not in its pipeline):
    # dependency-aware insertion, with and without the parking filter
    for seed, park in ((0, True), (1, False)):
        r = attempt(seed, strategy="deps", defer=True, park=park, stage="deps")
        if r:
            return r
    r = relaxed(16, 24, 8, "deep-relax")                      # fallback 2
    if r:
        return r
    from plan.followup import STAGE_PARAMS                    # fallback 3 (--cascade): follow-up stages
    for name in CASCADE:
        kw = STAGE_PARAMS[name]
        r = relaxed(kw["depth"], kw["beam"], kw["tries"], f"cascade-{name}", kw["planner_retries"])
        if r:
            return r
    return {"ok": False, "reason": last}


def _predecessor(T, sq, origin, victim):
    """T with the White piece on sq moved back to origin and `victim` on sq."""
    P = dict(T)
    piece = P.pop(sq)
    P[origin] = piece
    P[sq] = victim
    return P


def _work(args):
    from plan.flags import effective_states, realizable_flags, terminal_realizations
    from plan.moves import single_moves, usi
    stratum, seed, retries = args
    rng = random.Random(seed)
    t0 = time.time()
    rec = {"stratum": stratum, "seed": seed}
    from plan.lanes import lane_ok
    if stratum == "nonterm":
        T = _ctx["nonterm"].sample(rng)[0]
        rec["sfen"] = to_sfen(T)
        if not lane_ok(T):
            rec["result"] = {"ok": False, "unreachable": True, "reason": "I10: no wall-free entrance"}
        else:
            rec["result"] = _plan(T, retries)
    elif stratum in ("flags", "flagsj"):
        while True:                              # uniform over (board, flag state) pairs
            T = _ctx["nonterm"].sample(rng)[0]
            if stratum == "flags":
                es = effective_states(T)
            else:                                # JCSA states: banned move sets under sakishishi
                from jcsa.flags_jcsa import jcsa_states
                es = jcsa_states(_ctx["jeng"], T)
            assert len(es) <= KMAX, (to_sfen(T), len(es))
            if es and rng.random() < len(es) / KMAX:
                break
        if not lane_ok(T):
            rec["sfen"], rec["flag"] = to_sfen(T), list(es[0][0])
            rec["result"] = {"ok": False, "unreachable": True, "reason": "I10: no wall-free entrance"}
            rec["secs"] = round(time.time() - t0, 1)
            return rec
        l, banned = rng.choice(es)
        rec["sfen"], rec["flag"] = to_sfen(T), list(l)
        res = {"ok": False, "reason": "no realization"}
        tried = 0
        for prior_piece, a in realizable_flags(T)[l]:
            if tried >= 4:
                break
            P = dict(T)
            if l in T:                                   # capture on the destination square
                del P[l]
                P[a] = prior_piece
                P[l] = ("B", "N")
                tail = [usi(a, l, promote=prior_piece != T[l])]
            else:                                        # falcon/eagle igui or pass-through on l
                q = [s_ for s_, p in T.items() if p == prior_piece and (s_ == a or
                     (s_[0] - l[0], s_[1] - l[1]) == (l[0] - a[0], l[1] - a[1]))]
                if not q:
                    continue
                q = q[0]
                del P[q]
                P[a] = prior_piece
                P[l] = ("B", "N")
                tail = [usi(a, q, mid=l)]
            tried += 1
            res = _plan(P, retries, turn="W", tail=tail, target=T, flag=l, use_relax=(tried == 1))
            if res["ok"]:
                break
        rec["result"] = res
    else:
        T = _ctx["term"].sample(rng)[0]
        rec["sfen"] = to_sfen(T)
        real = terminal_realizations(T)
        if not lane_ok(T):
            rec["result"] = {"ok": False, "unreachable": True, "reason": "I10: no wall-free entrance"}
        elif not real:
            rec["result"] = {"ok": False, "unreachable": True, "reason": "retro: no capture of the last royal"}
        else:
            res = {"ok": False, "reason": "no realization"}
            for i, (prior_piece, s_, a) in enumerate(real[:5]):
                P = dict(T)
                del P[s_]
                P[a] = prior_piece
                P[s_] = ("B", "K")
                res = _plan(P, retries, turn="W", tail=[usi(a, s_, promote=prior_piece != T[s_])], target=T, use_relax=(i == 0))
                if res["ok"]:
                    break
            rec["result"] = res
    if rec["result"].get("ok"):
        # standing check: a certified (reachable) board must satisfy every invariant
        from plan.lanes import lane_ok as _lane_ok
        full = chu_setup("file", identify_royals=True, mover_royal_required=False)
        if not (is_candidate(full, T, "file", True) and _lane_ok(T)):
            rec["invariant_violation"] = True
    rec["secs"] = round(time.time() - t0, 1)
    return rec


def summarize(records, sizes):
    print()
    bad = [r for r in records if r.get("invariant_violation")]
    if bad:
        print(f"*** INVARIANT VIOLATION on {len(bad)} certified boards (an invariant is wrong): "
              f"{[r['sfen'] for r in bad[:3]]} ***")
    total_lo = total_hi = 0.0
    maxp = 0
    for s in ("nonterm", "flags", "flagsj", "term"):
        rs = [r for r in records if r["stratum"] == s]
        n = len(rs)
        if not n:
            continue
        if s == "flagsj":                      # JCSA flag stratum: printed, not part of the lishogi interval
            c = sum(r["result"]["ok"] for r in rs)
            cj = sum(bool(r["result"].get("ok") and r["result"].get("jcsa_ok")) for r in rs)
            proven = sum(r["result"].get("unreachable", False) for r in rs)
            print(f"flagsj   n={n}: certified {c} (replay under JCSA {cj}), proven unreachable {proven}, unresolved {n - c - proven}")
            continue
        c = sum(r["result"]["ok"] for r in rs)
        proven = sum(r["result"].get("unreachable", False) for r in rs)
        u = n - c - proven
        maxp = max([maxp] + [r["result"].get("plies", 0) for r in rs])
        p_lo, _ = clopper_pearson(c, n)
        _, p_hi = clopper_pearson(c + u, n)
        base = "nonterm" if s == "flags" else s
        sh, sh_se = I10_SHARE[base]
        c_lo, c_hi = sizes[base] * (1 - sh - 3 * sh_se), sizes[base] * (1 - sh + 3 * sh_se)   # I10 applied to the cap
        if s == "flags":
            w_lo, w_hi = c_lo * (EK - 3 * EK_SE), c_hi * (EK + 3 * EK_SE)
        else:
            w_lo, w_hi = c_lo, c_hi
        lo, hi = w_lo * p_lo, w_hi * p_hi
        total_lo += lo
        total_hi += hi
        stages = {}
        for r in rs:
            if r["result"]["ok"]:
                st = r["result"].get("stage", "baseline")
                stages[st] = stages.get(st, 0) + 1
        print(f"         certified by stage (additive): {stages}")
        if JCSA or any("jcsa_ok" in r["result"] for r in rs):
            cj = sum(bool(r["result"].get("ok") and r["result"].get("jcsa_ok")) for r in rs)
            fails = {}
            for r in rs:
                f = r["result"].get("jcsa_fail")
                if f:
                    fails[f["category"]] = fails.get(f["category"], 0) + 1
            print(f"         replay under JCSA: {cj} of {c} certificates hold; failures {fails}")
        rescued = sorted(r["result"]["rescued"] for r in rs if r["result"].get("rescued"))
        reasons = {}
        for r in rs:
            if not r["result"]["ok"]:
                k = r["result"]["reason"].split(":")[0][:40]
                reasons[k] = reasons.get(k, 0) + 1
        print(f"{s:8s} n={n}: certified {c}, proven unreachable {proven}, unresolved {u} ({u / n:.4f});"
              f" p in [{p_lo:.5f}, {p_hi:.5f}] (Clopper-Pearson 99.73 %); contribution [{lo:.4e}, {hi:.4e}]")
        if rescued:
            print(f"         rescued by relaxation: {len(rescued)}, retraction plies {rescued}")
        if reasons:
            print(f"         unresolved reasons: {reasons}")
    mid = (total_lo + total_hi) / 2
    print(f"|R| (Black to move) in [{total_lo:.4e}, {total_hi:.4e}], mid {mid:.4e},"
          f" relative half-width {(total_hi - total_lo) / 2 / mid:.2e}; x2 for either side to move:"
          f" [{2 * total_lo:.4e}, {2 * total_hi:.4e}]; longest game {maxp} plies")
    print(f"two significant digits: {'QUALIFIES' if 1.95e164 <= total_lo and total_hi < 2.05e164 else 'does not qualify'}"
          f" (needs [1.95, 2.05)e164)")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, required=True)
    ap.add_argument("--nonterm", type=int, default=100)
    ap.add_argument("--flags", type=int, default=20)
    ap.add_argument("--term", type=int, default=10)
    ap.add_argument("--flagsj", type=int, default=0, help="JCSA flag-state samples (needs --jcsa)")
    ap.add_argument("--jcsa", action="store_true", help="dual-rule run: replay every certificate under JCSA")
    ap.add_argument("--procs", type=int, default=8)
    ap.add_argument("--retries", type=int, default=6)
    ap.add_argument("--tag", default=None)
    ap.add_argument("--resume", action="store_true", help="keep the records already in the output file and append")
    ap.add_argument("--maxtasks", type=int, default=None, help="recycle each worker after this many jobs")
    ap.add_argument("--planner", choices=("python", "cpp"), default="python")
    ap.add_argument("--cascade", default="", help="comma-separated follow-up stages, e.g. A,B,C,D")
    ap.add_argument("--fix-relax-turn", action="store_true",
                    help="relax() certifies against the target's side to move (even depths too; relax.py)")
    ap.add_argument("--wide-seeds", action="store_true",
                    help="stratum seed offsets 0 / 10^6 / 2*10^6 / 3*10^6 (term / flags / flagsj / nonterm), "
                         "so that no two strata share a seed at any sample size")
    args = ap.parse_args()
    cascade = tuple(c for c in args.cascade.split(",") if c)
    sizes = {"nonterm": count(chu_setup("file", identify_royals=True), "file", colour=True).total,
             "term": count(chu_setup("file", identify_royals=True, terminal_only=True), "file", colour=True).total}
    cap = sizes["nonterm"] * (1 - I10_SHARE["nonterm"][0]) * (1 + EK) + sizes["term"] * (1 - I10_SHARE["term"][0])
    print(f"|C_nt| = {sizes['nonterm']:.6e}, |C_t| = {sizes['term']:.6e}, E[k] = {EK:.5f} +- {3 * EK_SE:.5f} (3σ),"
          f" I10 shares {I10_SHARE['nonterm'][0]:.5f} / {I10_SHARE['term'][0]:.5f}; cap = {cap:.4e}", flush=True)
    print(f"planner {args.planner}, cascade {cascade or 'none'}, fix_relax_turn {args.fix_relax_turn},"
          f" wide_seeds {args.wide_seeds}, retries {args.retries}", flush=True)
    off = (0, 1000000, 2000000, 3000000) if args.wide_seeds else (0, 10000, 30000, 20000)
    base = args.seed * (10000019 if args.wide_seeds else 1000003)
    jobs = [("term", base + off[0] + i, args.retries) for i in range(args.term)]
    jobs += [("flags", base + off[1] + i, args.retries) for i in range(args.flags)]
    jobs += [("flagsj", base + off[2] + i, args.retries) for i in range(args.flagsj)]
    jobs += [("nonterm", base + off[3] + i, args.retries) for i in range(args.nonterm)]
    tag = args.tag or f"estimate_seed{args.seed}_{args.nonterm}_{args.flags}_{args.term}" + (f"_{args.flagsj}j" if args.jcsa else "")
    out = Path("out/runs") / f"{tag}.jsonl"
    out.parent.mkdir(parents=True, exist_ok=True)
    records = []
    if args.resume and out.exists():
        lines = out.read_text().splitlines()
        try:
            json.loads(lines[-1])
        except (IndexError, ValueError):            # a record cut off by the interruption
            lines = lines[:-1]
            out.write_text("".join(l + "\n" for l in lines))
        records = [json.loads(l) for l in lines]
        seen = {(r["stratum"], r["seed"]) for r in records}
        jobs_left = [j for j in jobs if (j[0], j[1]) not in seen]
        print(f"resuming: {len(records)} records already in {out}", flush=True)
    else:
        jobs_left = jobs
    t0 = time.time()
    with Pool(args.procs, initializer=_init, initargs=(args.jcsa, args.planner, cascade, args.fix_relax_turn),
              maxtasksperchild=args.maxtasks) as pool, out.open("a" if args.resume else "w") as fh:
        for i, rec in enumerate(pool.imap_unordered(_work, jobs_left), len(records)):
            records.append(rec)
            fh.write(json.dumps(rec) + "\n")
            fh.flush()
            if (i + 1) % 10 == 0:
                ok = sum(r["result"]["ok"] for r in records)
                print(f"  ... {i + 1}/{len(jobs)} done, {ok} certified, {time.time() - t0:.0f}s", flush=True)
    summarize(records, sizes)
    registered_brackets(records, sizes)


def _cp_lower(c, n, alpha):
    from plan.budget import cp_lower
    return cp_lower(c, n, alpha)


def registered_brackets(records, sizes):
    """The registered statement (runs.md, M-D): Bonferroni over NCOMP components,
    one-sided ALPHA each; I10-violating samples excluded from the denominators (the cap
    removes the I10 share); unresolved samples count as unreachable.  Printed for
    lishogi and, in a dual-rule run, for JCSA (certificates that replay under JCSA,
    the JCSA flag stratum with the paired E[k]_JCSA)."""
    from statistics import NormalDist
    z = NormalDist().inv_cdf(1 - ALPHA)
    s_nt, s_nt_se = I10_SHARE["nonterm"]
    s_t, s_t_se = I10_SHARE["term"]
    cap = sizes["nonterm"] * (1 - s_nt) * (1 + EK) + sizes["term"] * (1 - s_t)
    cnt, ct = sizes["nonterm"] * (1 - s_nt - z * s_nt_se), sizes["term"] * (1 - s_t - z * s_t_se)

    def stratum(name, ok):
        rs = [r for r in records if r["stratum"] == name]
        n = sum(1 for r in rs if not r["result"].get("unreachable"))
        c = sum(1 for r in rs if ok(r["result"]))
        return c, n

    print()
    for rules in (("lishogi",) + (("JCSA",) if JCSA or any(r["stratum"] == "flagsj" for r in records) else ())):
        if rules == "lishogi":
            ok = lambda res: bool(res.get("ok"))
            c1, n1 = stratum("nonterm", ok)
            c2, n2 = stratum("flags", ok)
            c3, n3 = stratum("term", ok)
            ek, ek_se = EK, EK_SE
        else:
            ok = lambda res: bool(res.get("ok")) and bool(res.get("jcsa_ok"))
            c1, n1 = stratum("nonterm", ok)
            c2, n2 = stratum("flagsj", ok)
            c3, n3 = stratum("term", ok)
            ek, ek_se = EK_JCSA, EK_JCSA_SE
            if ek is None:
                print("JCSA bracket: E[k]_JCSA not entered (EK_JCSA); skipped")
                continue
        if not (n1 and n2 and n3):
            print(f"{rules} bracket: a stratum is empty ({n1}, {n2}, {n3}); skipped")
            continue
        p1, p2, p3 = _cp_lower(c1, n1, ALPHA), _cp_lower(c2, n2, ALPHA), _cp_lower(c3, n3, ALPHA)
        lo = cnt * p1 + cnt * (ek - z * ek_se) * p2 + ct * p3
        cap_r = sizes["nonterm"] * (1 - s_nt) * (1 + ek) + sizes["term"] * (1 - s_t)
        width = (cap_r - lo) / cap_r
        print(f"{rules} registered bracket: |R| in [{lo:.5e}, {cap_r:.5e}] (Black to move), width {width * 100:.3f} %;"
              f" x2 [{2 * lo:.4e}, {2 * cap_r:.4e}]; p1 {c1}/{n1} >= {p1:.5f}, p2 {c2}/{n2} >= {p2:.5f}, p3 {c3}/{n3} >= {p3:.5f};"
              f" E[k] {ek:.5f}; Bonferroni over {NCOMP}, one-sided alpha {ALPHA:.2e}"
              + (f"; width <= 0.5 %: {'QUALIFIES' if width <= 0.005 else 'does not qualify'}" if rules == "lishogi" else ""))


if __name__ == "__main__":
    main()
