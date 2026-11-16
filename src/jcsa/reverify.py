#!/usr/bin/env python3
"""Re-verify an estimator run's certificates under JCSA rules.

The estimator does not store move lists, but its pipeline is deterministic per
(stratum, seed, retries): re-running `plan.estimate._work` on a record regenerates
the same certificate.  The successful `certify` call is intercepted to capture the
moves, which are then replayed through a lishogi engine (for the state and flag)
while a second engine answers `jcsa.legal_moves` at every ply.  A certificate
"holds under JCSA" iff every move is JCSA-legal; failures are categorised.

Usage: python3 src/jcsa/reverify.py out/runs/X.jsonl --procs 4 [--sample 1000 --seed 1] [--out out/runs/X_jcsa.jsonl]
"""
import argparse
import json
import random
import sys
import time
from multiprocessing import Pool
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

_cap = {}


def _init(mates=False):
    global MATES
    MATES = mates
    import plan.certify as cert
    import plan.estimate as est
    from plan.engine import Engine
    est._init(jcsa=True)          # the flagsj stratum (M-D on) needs the JCSA engines
    real = cert.certify

    def capturing_certify(moves, target, **kw):
        ok, why = real(moves, target, **kw)
        if ok:
            _cap["moves"] = list(moves)
        return ok, why
    cert.certify = capturing_certify            # estimate.py imports it at call time
    _cap["eng"] = Engine()          # replays the game (lishogi state incl. flag)
    _cap["jeng"] = Engine()         # answers JCSA legality / mate queries


MATES = False      # --mates: also count mated positions along the game (U10); ~10x slower


def verify_jcsa(moves):
    from jcsa.mode import replay_jcsa
    return replay_jcsa(moves, _cap["eng"], _cap["jeng"], count_mates=MATES)


def _work(rec):
    import plan.estimate as est
    t0 = time.time()
    _cap.pop("moves", None)
    out = {"stratum": rec["stratum"], "seed": rec["seed"], "sfen": rec["sfen"], "stage": rec["result"].get("stage")}
    r = est._work((rec["stratum"], rec["seed"], 6))
    out["regenerated_ok"] = bool(r["result"].get("ok"))
    out["same_as_run"] = (bool(r["result"].get("ok")) == bool(rec["result"].get("ok")))
    if out["regenerated_ok"] and "moves" in _cap:
        ok, ply, mv, cat, mates = verify_jcsa(_cap["moves"])
        out.update(jcsa_ok=ok, plies=len(_cap["moves"]), fail_ply=ply, fail_move=mv, category=cat,
                   mate_plies=mates[:10], n_mates=len(mates))
    out["secs"] = round(time.time() - t0, 1)
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("jsonl")
    ap.add_argument("--procs", type=int, default=4)
    ap.add_argument("--sample", type=int, default=0, help="random subset of the certified records")
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--out", default=None)
    ap.add_argument("--mates", action="store_true", help="count JCSA-mated positions along each game (slow)")
    a = ap.parse_args()
    recs = [json.loads(l) for l in open(a.jsonl)]
    recs = [r for r in recs if r["result"].get("ok")]
    if a.sample:
        recs = random.Random(a.seed).sample(recs, min(a.sample, len(recs)))
    out = Path(a.out or a.jsonl.replace(".jsonl", f"_jcsa{'_s' + str(a.sample) if a.sample else ''}.jsonl"))
    n = ok = regen = with_mates = 0
    cats = {}
    t0 = time.time()
    with Pool(a.procs, initializer=_init, initargs=(a.mates,)) as pool, out.open("w") as fh:
        for r in pool.imap_unordered(_work, recs):
            n += 1
            regen += r["regenerated_ok"]
            ok += bool(r.get("jcsa_ok"))
            if r.get("jcsa_ok") is False:
                cats[r["category"]] = cats.get(r["category"], 0) + 1
            with_mates += bool(r.get("n_mates"))
            fh.write(json.dumps(r) + "\n")
            fh.flush()
            if n % 50 == 0:
                print(f"  ... {n}/{len(recs)} regenerated {regen} JCSA-ok {ok} fails {cats} {time.time() - t0:.0f}s", flush=True)
    print(f"{len(recs)} certified records: regenerated {regen}, hold under JCSA {ok}, fail by category {cats};"
          f" games passing through a mated position (U10): {with_mates}; {time.time() - t0:.0f}s")


if __name__ == "__main__":
    main()
