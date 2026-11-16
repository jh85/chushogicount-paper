#!/usr/bin/env python3
"""Verification of run G13b's certificates (D13 with D13a and D13b): regenerate a random sample
of certified boards and replay each game independently of chu-plan.

Sample: --n boards from the certified records of G13 (not rerun) and of G13b's redo set,
random.Random(--seed).  Each board is regenerated with the binary that certified it:
G13 boards with --plan-a (.engines/chu-plan-d13p2), G13b boards with --plan-b
(.engines/chu-plan-d13b), the attempt list of d13_pilot.py --pipeline v2.  Checks:
  regen    the regenerated record has the run's route, attempt seed, strategy and ply count
  legal    every move is legal in the native engine under `rules jcsa`, and the final board
           (Black to move) is the target
  mates    no position before the last has the side to move mated, by the Python reference
           jcsa/mode.py mated(prince_escape=True, capture_escape=True) on the native engine:
           D13 with D13a and D13b, independent of chu-plan's mate test

--all-g13b: instead of the sample, every board certified in G13b's redo set (the certificates
that depend on the D13b mate test).

Usage: python3 src/jcsa/verify_d13.py --n 2000 --procs 16 [--out out/runs/d13_verify_g13b.jsonl]
       python3 src/jcsa/verify_d13.py --all-g13b --procs 16 --out out/runs/d13_verify_g13b_redo.jsonl
CHU_ENGINE / CHU_ENGINE_JCSA as for d13_pilot.py.
"""
import argparse
import json
import random
import sys
import time
from collections import Counter
from multiprocessing import Pool
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
_c = {}
KEYS = ("route", "attempt_seed", "strategy", "plies")


def _init(plan_a, plan_b):
    from jcsa import d13_pilot
    from jcsa.native import NativeEngine
    from plan.cplanner import CPlan
    d13_pilot._init("v2")
    _c["cp"] = {"G13": CPlan(plan_a), "G13b": CPlan(plan_b)}
    _c["nj"], _c["nm"] = NativeEngine("jcsa"), NativeEngine("jcsa")


def regenerate(T):
    """The certificate d13_pilot.work would find (same attempt order), as a move list."""
    from jcsa import d13_pilot as dp
    from plan.mateplan import PRED_STRATEGIES, plan_d13
    res = plan_d13(T, dp._c["cp"], dp._c["eng"], pipeline="v2")
    if res["ok"]:
        return res["moves"], {k: res.get(k) for k in ("route", "seed", "strategy")}
    kind, _, _ = dp._retract(T)
    if kind != "reachable":
        return None, {}
    me = dp._c["me"]
    r2 = me.retract2(T, dp._c["cp"])
    if r2[0] == "budget":
        r2 = me.retract2(T, dp._c["cp"], max_q=200000)
    if r2[0] == "unreachable":
        return None, {}
    game = dp._plan_q2(T, r2[1], r2[2]) if r2[0] == "reachable" else None
    if not game:
        for pm, qm in me.chains2(T, dp._c["cp"], max_q=200000, royal_only=True) + me.chains2(T, dp._c["cp"]):
            game = dp._plan_q2(T, pm, qm, kws=PRED_STRATEGIES)
            if game:
                break
    return game, {"route": "q2"}


def check(moves, T):
    """(legal and target reached, plies at which the side to move is mated before the end)."""
    from count.sfen import INITIAL, parse
    from jcsa.mode import mated
    nj = _c["nj"]
    nj.position(INITIAL)
    mates = []
    for i, mv in enumerate(moves):
        board, turn, flag = parse(nj.sfen())
        if mated(_c["nm"], board, turn, flag, True, True):
            mates.append(i)
        if mv not in nj.legal():
            return False, mates, f"illegal at ply {i}: {mv}"
        nj.move(mv)
    board, turn, _ = parse(nj.sfen())
    if board != T or turn != "B":
        return False, mates, "final position differs"
    return True, mates, ""


def work(item):
    from count.sfen import parse
    from jcsa import d13_pilot as dp
    src, rec, sfen = item
    t0 = time.time()
    dp._c["cp"] = _c["cp"][src]
    T = parse(sfen)[0]
    moves, info = regenerate(T)
    out = {"seed": rec["seed"], "source": src}
    if not moves:
        out.update(regen=False, legal=False, mates=None, why="not regenerated")
    else:
        got = {"route": info.get("route"), "attempt_seed": info.get("seed"), "strategy": info.get("strategy"),
               "plies": len(moves)}
        out["regen"] = all(got[k] == rec[k] for k in KEYS if k in rec)
        if not out["regen"]:
            out["diff"] = {k: (rec[k], got[k]) for k in KEYS if k in rec and got[k] != rec[k]}
        ok, mates, why = check(moves, T)
        out.update(legal=ok, mates=len(mates), why=why)
    out["secs"] = round(time.time() - t0, 1)
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--g13", required=True)
    ap.add_argument("--g13b", required=True)
    ap.add_argument("--records", required=True)
    ap.add_argument("--plan-a", required=True)
    ap.add_argument("--plan-b", required=True)
    ap.add_argument("--n", type=int, default=2000)
    ap.add_argument("--seed", type=int, default=20261026)
    ap.add_argument("--procs", type=int, default=16)
    ap.add_argument("--out", default="out/runs/d13_verify_g13b.jsonl")
    ap.add_argument("--all-g13b", action="store_true")
    a = ap.parse_args()
    redo = {r["seed"]: r for r in map(json.loads, open(a.g13b))}
    pool_ = [("G13b", r) for r in redo.values() if r["d13"] == "certified"]
    pool_ += [("G13", r) for r in map(json.loads, open(a.g13)) if r["d13"] == "certified" and r["seed"] not in redo]
    pool_.sort(key=lambda x: x[1]["seed"])
    pick = [x for x in pool_ if x[0] == "G13b"] if a.all_g13b else random.Random(a.seed).sample(pool_, a.n)
    want = {r["seed"] for _, r in pick}
    sfen = {}
    for line in open(a.records):
        r = json.loads(line)
        if r["stratum"] == "nonterm" and r["seed"] in want:
            sfen[r["seed"]] = r["sfen"]
    items = [(s, r, sfen[r["seed"]]) for s, r in pick]
    print(f"{len(pool_)} certified boards, sample {len(items)} "
          f"({Counter(s for s, _, _ in items)}), seed {a.seed} -> {a.out}", flush=True)
    rows = []
    with Pool(a.procs, _init, (a.plan_a, a.plan_b), maxtasksperchild=50) as pool, open(a.out, "w") as fh:
        for k, row in enumerate(pool.imap_unordered(work, items), 1):
            fh.write(json.dumps(row) + "\n")
            fh.flush()
            rows.append(row)
            if k % 100 == 0:
                print(f"  ... {k}/{len(items)}", flush=True)
    n = len(rows)
    print(f"{n} boards: regenerated identically {sum(r['regen'] for r in rows)}, "
          f"legal under rules jcsa with the target reached {sum(r['legal'] for r in rows)}, "
          f"no mated position before the end (Python D13/D13a/D13b) {sum(r['mates'] == 0 for r in rows)}")
    bad = [r for r in rows if not (r["regen"] and r["legal"] and r["mates"] == 0)]
    print("failures:", bad[:10])


if __name__ == "__main__":
    main()
