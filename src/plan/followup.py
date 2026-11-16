#!/usr/bin/env python3
"""Follow-up on the unresolved non-terminal boards of a main run (exploratory; runs.md,
"M-E follow-up").  Each board goes through a cascade of deeper retro-relaxation stages,
stopping at the first success:
  A: depth 32, beam 48, tries 16, planner retries 4
  B: depth 64, beam 48, tries 16, planner retries 4
Second follow-up (runs.md, "M-E follow-up 2", on the boards the first one left unresolved):
  C: depth 128, beam 48, tries 16, planner retries 4      (deeper)
  D: depth 64, beam 192, tries 64, planner retries 8      (wider; planner seeds 0-7)
A found game counts only if the certifier replays it to the target (lishogi); it is also
replayed under JCSA.  Nothing here proves unreachability: a board that fails every stage
stays unresolved.  The search is deterministic (planner seeds are the attempt numbers).

Usage: python3 src/plan/followup.py out/runs/<main>.jsonl --out out/runs/<main>_followup.jsonl --procs 14
       [--resume] [--maxtasks 1]   (resume after an interruption; recycle workers to free memory)
       [--stages C,D --skip out/runs/<main>_followup.jsonl]   (second follow-up: skip boards certified there)
"""
import argparse
import json
import sys
import time
from multiprocessing import Pool
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

STAGE_PARAMS = {"A": dict(depth=32, beam=48, tries=16, planner_retries=4),
                "B": dict(depth=64, beam=48, tries=16, planner_retries=4),
                "C": dict(depth=128, beam=48, tries=16, planner_retries=4, compact_seen=True),
                "D": dict(depth=64, beam=192, tries=64, planner_retries=8, compact_seen=True)}
STAGES = (("A", STAGE_PARAMS["A"]), ("B", STAGE_PARAMS["B"]))
_ctx = {}


def _init(stages=STAGES):
    from plan.engine import Engine
    _ctx["engine"], _ctx["replay"], _ctx["jeng"] = Engine(), Engine(), Engine()
    _ctx["stages"] = stages


def _work(rec):
    from count.sfen import parse
    from plan.certify import certify
    from plan.relax import relax
    from jcsa.mode import replay_jcsa
    T = parse(rec["sfen"])[0]
    out = {"seed": rec["seed"], "sfen": rec["sfen"], "first_reason": rec["result"].get("reason"),
           "certified": False, "stages": []}
    t0 = time.time()
    for name, kw in _ctx["stages"]:
        t1 = time.time()
        moves, info = relax(T, _ctx["engine"], **kw)
        st = {"stage": name, "found": bool(moves), "tried": info["tried"], "levels": info["levels"],
              "secs": round(time.time() - t1)}
        out["stages"].append(st)
        if moves:
            ok, why = certify(moves, T, engine=_ctx["engine"])
            st.update(certified=ok, why=why)
            if ok:
                jok, ply, mv, cat, _ = replay_jcsa(moves, _ctx["replay"], _ctx["jeng"])
                out.update(certified=True, stage=name, plies=len(moves), retracted=info.get("retracted"),
                           jcsa_ok=jok, jcsa_fail=None if jok else {"ply": ply, "move": mv, "category": cat},
                           moves=moves)
                break
    out["secs"] = round(time.time() - t0)
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("records")
    ap.add_argument("--out", required=True)
    ap.add_argument("--procs", type=int, default=14)
    ap.add_argument("--resume", action="store_true", help="skip boards already in --out and append")
    ap.add_argument("--maxtasks", type=int, default=None, help="recycle each worker after this many boards")
    ap.add_argument("--stages", default="A,B", help="comma-separated stage names from STAGE_PARAMS")
    ap.add_argument("--skip", help="a previous follow-up's jsonl: skip the boards it certified")
    a = ap.parse_args()
    stages = tuple((s, STAGE_PARAMS[s]) for s in a.stages.split(","))
    recs = [json.loads(l) for l in open(a.records)]
    todo = [r for r in recs if r["stratum"] == "nonterm" and not r["result"].get("ok")
            and not r["result"].get("unreachable")]
    if a.skip:
        prev = {r["seed"] for r in map(json.loads, open(a.skip)) if r["certified"]}
        todo = [r for r in todo if r["seed"] not in prev]
    print(f"{len(todo)} unresolved non-terminal boards; stages {[(s, kw) for s, kw in stages]}", flush=True)
    t0, n, ok = time.time(), 0, 0
    if a.resume and Path(a.out).exists():
        done = [json.loads(l) for l in open(a.out)]
        seen = {r["seed"] for r in done}
        n, ok = len(done), sum(r["certified"] for r in done)
        print(f"resuming: {n} boards already in {a.out} ({ok} certified)", flush=True)
    else:
        seen = set()
    rest = [r for r in todo if r["seed"] not in seen]
    with Pool(a.procs, initializer=_init, initargs=(stages,), maxtasksperchild=a.maxtasks) as pool, \
            open(a.out, "a" if a.resume else "w") as fh:
        for r in pool.imap_unordered(_work, rest):
            n += 1
            ok += r["certified"]
            fh.write(json.dumps(r) + "\n")
            fh.flush()
            print(f"  {n}/{len(todo)} seed {r['seed']}: {'certified at ' + r['stage'] if r['certified'] else 'unresolved'}"
                  f" ({r['secs']} s); certified so far {ok}", flush=True)
    by = {}
    for r in map(json.loads, open(a.out)):
        if r["certified"]:
            by[r["stage"]] = by.get(r["stage"], 0) + 1
    print(f"{len(todo)} boards: certified {ok} (by stage {by}), still unresolved {len(todo) - ok}; {time.time() - t0:.0f}s")


if __name__ == "__main__":
    main()
