#!/usr/bin/env python3
"""D13 pilot: how many non-terminal candidate boards stay reachable under the literal JCSA
checkmate ending (docs/decisions.md D13)?

Input: the records of an estimate.py run (a uniform sample of the stratum, consecutive
seeds); the first --n boards of --stratum after --offset are reclassified under D13:
  I10          proven unreachable (I10, docs/invariants.md: its proof uses piece geometry
               only, so it holds for JCSA move rules and for D13 games too)
  certified    a game with no mated position before the end, checked by
               plan/mateplan.py certify_d13 (plan/certify.py + a JCSA replay in chu-plan);
               route "direct" (MatePlanner to T), "relax" (relax_d13: retro-relaxation to a plain base,
               every retracted position un-mated) or "pred" (MatePlanner to a predecessor P,
               White to move and not mated, then White's last move: 8 non-capturing
               retractions, then 4 more from the complete one-ply retraction)
  retracted    proven unreachable: every legal candidate predecessor (complete one-ply
               retraction, jcsa/mate_ending.py retract) has White mated in it (D13 test,
               no flag: the weakest case); then the game would have ended in P
  retracted2   proven unreachable by two plies (mate_ending.retract2): every legal candidate
               P has White mated or only predecessors Q with Black mated (budget 20 000 Q;
               pipeline v2: then 200 000); if it finds a Q with Black not mated, MatePlanner to
               Q then the two moves (route "q2"; v2 also on the royal-first chains of
               mate_ending.chains2, also after a budget stop)
  unresolved   none of these (counted as unreachable in any bound)
The attempt list is fixed (plan_d13: 6 seeds direct, then 8 + 4 predecessors x 2 seeds), so a
record depends on the board and the code only.  The D10 result of the input record is kept.

Usage: python3 src/jcsa/d13_pilot.py out/runs/estimate_seed192_400000_40000_24000_40000j.jsonl \\
           --n 1500 --procs 6 --maxtasks 50 [--offset 0] [--resume] [--out out/runs/d13_pilot_X.jsonl]
CHU_ENGINE / CHU_ENGINE_JCSA should name the runs' engine (.engines/chushogi-gen-me).
"""
import argparse
import json
import sys
import time
from collections import Counter
from multiprocessing import Pool
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
_c = {}
PIPELINE = "p2"             # --pipeline (plan/mateplan.py plan_d13)


def _init(pipeline="p2"):
    global PIPELINE
    PIPELINE = pipeline                     # workers may not be forked (3.14: forkserver)
    from plan.cplanner import CPlan
    from plan.engine import Engine
    _c["cp"], _c["eng"] = CPlan(), Engine()
    _c["me"] = None


def _retract(T):
    if _c["me"] is None:
        from jcsa import mate_ending
        if mate_ending._E is None:
            mate_ending._init(sampler=False)
        _c["me"] = mate_ending
    return _c["me"].retract(T, _c["cp"])


def _plan_q2(T, pm, qm, seeds=(0, 1), kws=None):
    """The two-ply route: MatePlanner to retract2's Q (Black to move, not mated), then
    Black's move into P and White's move into T; certify_d13."""
    from plan.mateplan import MatePlanner, PlannerError, Repetition, certify_d13
    (P, mv), (Q, mq) = pm, qm
    for s, kw in (kws or [(s, {}) for s in seeds]):
        p = MatePlanner(Q, _c["eng"], cp=_c["cp"], seed=s, end_turn="B", **kw)
        try:
            moves = p.run()
        except (PlannerError, Repetition):
            continue
        except Exception:                           # the planner's own bookkeeping errors
            continue
        game = moves + [mq, mv]
        if certify_d13(game, T, _c["cp"], engine=_c["eng"])[0]:
            return game
    return None


def work(rec):
    from count.sfen import parse
    from plan.lanes import lane_ok
    from plan.mateplan import plan_d13
    t0 = time.time()
    T = parse(rec["sfen"])[0]
    d10 = rec["result"].get("ok") and "certified" or ("unreachable" if rec["result"].get("unreachable") else "unresolved")
    out = {"seed": rec["seed"], "stratum": rec["stratum"], "d10": d10}
    if not lane_ok(T):
        out["d13"] = "I10"
    else:
        res = plan_d13(T, _c["cp"], _c["eng"], pipeline=PIPELINE)
        if res["ok"]:
            out.update(d13="certified", route=res["route"], attempt_seed=res["seed"], fixes=res["fixes"],
                       plies=len(res["moves"]))
            for k in ("strategy", "relax_depth", "retracted"):
                if k in res:
                    out[k] = res[k]
        else:
            kind, n_pred, mv = _retract(T)
            out.update(d13="retracted" if kind == "unreachable" else "unresolved", reason=res["reason"],
                       black_mated=res["black_mated"], white_caged=res["white_caged"], retract=[kind, n_pred, mv])
            if kind == "reachable":
                r2 = _c["me"].retract2(T, _c["cp"])
                if r2[0] == "budget" and PIPELINE == "v2":
                    r2 = _c["me"].retract2(T, _c["cp"], max_q=200000)
                out["retract2"] = [r2[0]] + ([r2[1], r2[2]] if r2[0] != "reachable" else [r2[1][1], r2[2][1]])
                if r2[0] == "unreachable":
                    out["d13"] = "retracted2"
                elif r2[0] == "reachable" or PIPELINE == "v2":
                    game = _plan_q2(T, r2[1], r2[2]) if r2[0] == "reachable" else None
                    if not game and PIPELINE == "v2":
                        from plan.mateplan import PRED_STRATEGIES
                        chains = _c["me"].chains2(T, _c["cp"], max_q=200000, royal_only=True) \
                            + _c["me"].chains2(T, _c["cp"])
                        for pm, qm in chains:
                            game = _plan_q2(T, pm, qm, kws=PRED_STRATEGIES)
                            if game:
                                break
                    if game:
                        for k in ("reason", "black_mated", "white_caged"):
                            out.pop(k)
                        out.update(d13="certified", route="q2", plies=len(game))
    out["secs"] = round(time.time() - t0, 1)
    return out


def summarize(rows):
    c = Counter(r["d13"] for r in rows)
    n = len(rows)
    print(f"{n} boards: " + ", ".join(f"{k} {v} ({v / n:.2%})" for k, v in sorted(c.items())))
    print("routes:", dict(Counter(r.get("route") for r in rows if r["d13"] == "certified")))
    print("retract2 on the rest:", dict(Counter(r["retract2"][0] for r in rows if "retract2" in r)))
    print("D10 x D13:", dict(Counter((r["d10"], r["d13"]) for r in rows)))
    print("unresolved (black mated, white caged):",
          dict(Counter((r["black_mated"], r["white_caged"]) for r in rows if r["d13"] == "unresolved")))
    print(f"secs: total {sum(r['secs'] for r in rows):.0f}, max {max(r['secs'] for r in rows):.0f}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("records")
    ap.add_argument("--stratum", default="nonterm")
    ap.add_argument("--n", type=int, default=1500)
    ap.add_argument("--offset", type=int, default=0)
    ap.add_argument("--procs", type=int, default=4)
    ap.add_argument("--maxtasks", type=int, default=50)
    ap.add_argument("--resume", action="store_true")
    ap.add_argument("--out")
    ap.add_argument("--pipeline", default="p2", choices=("p2", "v2"),
                    help="p2: pilot P2's attempt list; v2: docs/d13-planner.md step 1 and later")
    ap.add_argument("--seeds", help="only these record seeds (comma-separated file of seeds, one per line)")
    args = ap.parse_args()
    global PIPELINE
    PIPELINE = args.pipeline
    out = Path(args.out or f"out/runs/d13_pilot_{Path(args.records).stem}_{args.stratum}_{args.offset}_{args.n}.jsonl")
    out.parent.mkdir(parents=True, exist_ok=True)
    recs = [r for r in map(json.loads, open(args.records)) if r["stratum"] == args.stratum]
    recs.sort(key=lambda r: r["seed"])
    recs = recs[args.offset:args.offset + args.n]
    if args.seeds:
        keep = {int(x) for x in open(args.seeds).read().split()}
        recs = [r for r in recs if r["seed"] in keep]
    rows = []
    if args.resume and out.exists():
        lines = out.read_text().splitlines()
        for ln in lines:
            try:
                rows.append(json.loads(ln))
            except json.JSONDecodeError:            # a line cut off by a stop: dropped
                break
        out.write_text("".join(json.dumps(r) + "\n" for r in rows))
    done = {r["seed"] for r in rows}
    todo = [r for r in recs if r["seed"] not in done]
    print(f"{len(recs)} boards, {len(done)} already done, {len(todo)} to do -> {out}", flush=True)
    t0 = time.time()
    with Pool(args.procs, _init, (args.pipeline,), maxtasksperchild=args.maxtasks) as pool, out.open("a" if args.resume else "w") as fh:
        for k, row in enumerate(pool.imap_unordered(work, todo), 1):
            fh.write(json.dumps(row) + "\n")
            fh.flush()
            rows.append(row)
            if k % 25 == 0:
                c = Counter(r["d13"] for r in rows)
                print(f"  ... {len(rows)}/{len(recs)} {dict(c)} {time.time() - t0:.0f}s", flush=True)
    summarize(rows)


if __name__ == "__main__":
    main()
