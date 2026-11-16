#!/usr/bin/env python3
"""Differential test of chu-plan (src/plan/cpp) against the Python planner and relax.

For each board (main-run SFENs, parsed in dict order) and each planner configuration, the
Python Planner(...).run() and CPlan.plan(...) must give the same game, or fail with the same
exception type and message.  Configurations: the baseline (seeds 0, 1: greedy / peel), and on
the run's unresolved boards also the fallbacks (edge + deferral, seeds 101, 102; deps with and
without parking).  --relax also compares relax() (depth 10, beam 12, tries 4, retries 2) on
the unresolved boards (--fix-turn: both with fix_turn=True).  --followup F reruns the follow-up stages of F (out/runs/*_followup*.jsonl)
with chu-plan only and compares with the recorded outcome of every stage (found, tried,
levels) and the certified game.

Usage: python3 tests/test_cplanner.py [--n 2000] [--offset 0] [--procs 16] [--relax [--fix-turn]]
       [--unresolved] [--followup out/runs/<main>_followup.jsonl]
       [--records out/runs/estimate_seed191_40000_1000_600_1000j.jsonl] [--out out/runs/x.jsonl]
"""
import argparse
import json
import sys
import time
from multiprocessing import Pool
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "src"))

_ctx = {}
FIX_TURN = False
BASE = [dict(seed=0), dict(seed=1)]
FALLBACK = [dict(seed=101, strategy="edge", defer=True), dict(seed=102, strategy="edge", defer=True),
            dict(seed=0, strategy="deps", defer=True, park=True), dict(seed=1, strategy="deps", defer=True, park=False)]


def _init(fix_turn=False):
    global FIX_TURN
    FIX_TURN = fix_turn
    from plan.cplanner import CPlan
    from plan.engine import Engine
    _ctx["eng"], _ctx["cp"] = Engine(), CPlan()


def _py(T, kw):
    from plan.planner import Planner, PlannerError, Repetition
    try:
        return ["ok", Planner(T, _ctx["eng"], **kw).run()]
    except (PlannerError, Repetition) as e:
        return [type(e).__name__, str(e)]
    except Exception as e:
        return ["EXC", type(e).__name__, str(e)]


def _c(T, kw):
    from plan.cplanner import CPlanError
    from plan.planner import PlannerError, Repetition
    try:
        return ["ok", _ctx["cp"].plan(T, **kw)]
    except (PlannerError, Repetition) as e:
        return [type(e).__name__, str(e)]
    except CPlanError as e:
        return ["EXC", e.typ, str(e)]


def _work_followup(rec):
    from count.sfen import parse
    from plan.followup import STAGE_PARAMS
    T = parse(rec["sfen"])[0]
    out = []
    t0 = time.time()
    for st in rec["stages"]:
        kw = {k: v for k, v in STAGE_PARAMS[st["stage"]].items() if k != "compact_seen"}
        moves, info = _ctx["cp"].relax(T, **kw)
        got = {"found": bool(moves), "tried": info["tried"], "levels": info["levels"]}
        want = {k: st[k] for k in got}
        same = got == want and (not moves or moves == rec.get("moves"))
        out.append({"seed": rec["seed"], "cfg": "followup " + st["stage"], "same": same,
                    "py": want if not same else st["found"], "c": got if not same else None,
                    "tpy": st["secs"], "tc": round(time.time() - t0, 3)})
        t0 = time.time()
    return out


def _work(job):
    from count.sfen import parse
    from plan.relax import relax
    seed, sfen, kind = job
    T = parse(sfen)[0]
    out = []
    for kw in (BASE + FALLBACK if kind == "unresolved" else BASE):
        t0 = time.time()
        a = _py(T, kw)
        t1 = time.time()
        b = _c(T, kw)
        t2 = time.time()
        out.append({"seed": seed, "cfg": kw, "same": a == b, "py": a if a != b else a[0],
                    "c": b if a != b else None, "tpy": round(t1 - t0, 3), "tc": round(t2 - t1, 3)})
    if kind == "relax":
        t0 = time.time()
        ma, ia = relax(T, _ctx["eng"], depth=10, beam=12, tries=4, planner_retries=2, fix_turn=FIX_TURN)
        t1 = time.time()
        mb, ib = _ctx["cp"].relax(T, depth=10, beam=12, tries=4, planner_retries=2, fix_turn=FIX_TURN)
        t2 = time.time()
        out.append({"seed": seed, "cfg": "relax", "ok": bool(ma), "info": ia, "same": (ma, ia) == (mb, ib),
                    "py": [bool(ma), ia] if (ma, ia) != (mb, ib) else bool(ma),
                    "c": [bool(mb), ib] if (ma, ia) != (mb, ib) else None,
                    "tpy": round(t1 - t0, 3), "tc": round(t2 - t1, 3)})
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--records", required=True)
    ap.add_argument("--n", type=int, default=2000)
    ap.add_argument("--offset", type=int, default=0)
    ap.add_argument("--procs", type=int, default=16)
    ap.add_argument("--relax", action="store_true", help="relax() on the unresolved boards instead")
    ap.add_argument("--unresolved", action="store_true", help="planner fallbacks on the unresolved boards")
    ap.add_argument("--fix-turn", action="store_true", help="with --relax: relax(..., fix_turn=True) in both")
    ap.add_argument("--followup", help="a follow-up jsonl: rerun its stages with chu-plan and compare")
    ap.add_argument("--out")
    a = ap.parse_args()
    recs = [r for r in map(json.loads, open(a.records)) if r["stratum"] == "nonterm"
            and not r["result"].get("unreachable")]
    if a.followup:
        jobs = [json.loads(l) for l in open(a.followup)]
        jobs.sort(key=lambda r: -r["secs"])           # longest first
    elif a.relax or a.unresolved:
        jobs = [(r["seed"], r["sfen"], "relax" if a.relax else "unresolved") for r in recs if not r["result"].get("ok")]
    else:
        jobs = [(r["seed"], r["sfen"], "base") for r in recs[a.offset:a.offset + a.n]]
    t0, n, same, tpy, tc = time.time(), 0, 0, 0.0, 0.0
    fh = open(a.out, "w") if a.out else None
    with Pool(a.procs, initializer=_init, initargs=(a.fix_turn,)) as pool:
        for res in pool.imap_unordered(_work_followup if a.followup else _work, jobs, chunksize=1 if a.followup else 4):
            for r in res:
                n += 1
                same += r["same"]
                tpy += r["tpy"]
                tc += r["tc"]
                if fh:
                    fh.write(json.dumps(r) + "\n")
                if not r["same"]:
                    print("MISMATCH", json.dumps(r)[:600], flush=True)
    print(f"{len(jobs)} boards, {n} runs: identical {same}, different {n - same}; "
          f"time python {tpy:.0f} s, c++ {tc:.1f} s ({tpy / max(tc, 1e-9):.0f}x); wall {time.time() - t0:.0f} s")
    sys.exit(0 if same == n else 1)


if __name__ == "__main__":
    main()
