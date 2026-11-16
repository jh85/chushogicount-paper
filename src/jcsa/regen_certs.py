#!/usr/bin/env python3
"""Regenerate every certified record of an estimator run (deterministic per (stratum, seed))
and save the move lists: out/runs/<tag>_certs.jsonl.gz.  Usage: regen_certs.py out/runs/X.jsonl --procs 14
[--planner cpp --cascade A,B,C,D --fix-relax-turn] (the run's own settings; M-F) [--maxtasks 300]"""
import argparse, gzip, json, sys, time
from multiprocessing import Pool
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
_cap = {}


def _init(planner="python", cascade=(), fix_turn=False):
    import plan.certify as cert
    import plan.estimate as est
    est._init(jcsa=True, planner=planner, cascade=cascade, fix_turn=fix_turn)   # flagsj needs the JCSA engines
    real = cert.certify

    def capturing(moves, target, **kw):
        ok, why = real(moves, target, **kw)
        if ok:
            _cap["moves"] = list(moves)
        return ok, why
    cert.certify = capturing


def _work(rec):
    import plan.estimate as est
    _cap.pop("moves", None)
    t0 = time.time()
    r = est._work((rec["stratum"], rec["seed"], 6))
    return {"stratum": rec["stratum"], "seed": rec["seed"], "sfen": rec["sfen"], "flag": rec.get("flag"),
            "regenerated_ok": bool(r["result"].get("ok")), "same_as_run": bool(r["result"].get("ok")) == bool(rec["result"].get("ok")),
            "same_record": {k: v for k, v in r.items() if k != "secs"} == {k: v for k, v in rec.items() if k != "secs"},
            "moves": _cap.get("moves"), "secs": round(time.time() - t0, 1)}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("jsonl")
    ap.add_argument("--procs", type=int, default=14)
    ap.add_argument("--limit", type=int, default=0)
    ap.add_argument("--planner", choices=("python", "cpp"), default="python")
    ap.add_argument("--cascade", default="")
    ap.add_argument("--fix-relax-turn", action="store_true")
    ap.add_argument("--maxtasks", type=int, default=None)
    a = ap.parse_args()
    recs = [json.loads(l) for l in open(a.jsonl)]
    recs = [r for r in recs if r["result"].get("ok")]
    if a.limit:
        recs = recs[:a.limit]
    out = a.jsonl.replace(".jsonl", "_certs.jsonl.gz")
    n = ok = same = srec = 0
    t0 = time.time()
    cascade = tuple(c for c in a.cascade.split(",") if c)
    with Pool(a.procs, initializer=_init, initargs=(a.planner, cascade, a.fix_relax_turn),
              maxtasksperchild=a.maxtasks) as pool, gzip.open(out, "wt") as fh:
        for r in pool.imap_unordered(_work, recs):
            n += 1
            ok += bool(r["moves"])
            same += r["same_as_run"]
            srec += r["same_record"]
            fh.write(json.dumps(r) + "\n")
            if n % 500 == 0:
                print(f"  ... {n}/{len(recs)} regenerated {ok} same-as-run {same} same-record {srec} {time.time() - t0:.0f}s", flush=True)
    print(f"{len(recs)} certified records: regenerated with moves {ok}, same outcome as the run {same}, identical record {srec}; {time.time() - t0:.0f}s -> {out}")


if __name__ == "__main__":
    main()
