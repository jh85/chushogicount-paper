#!/usr/bin/env python3
"""Run the proof-game planner on uniformly sampled candidates.

Usage: python3 src/plan/run.py [--n 50] [--seed 1] [--verbose]
Prints, per sample, success (with ply count, verified by an independent replay)
or the failing phase and reason, then a summary.
"""
import argparse
import random
import sys
import time
import traceback
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from count.candidates import PRIMARY, chu_setup          # noqa: E402
from count.sampler import Sampler, to_sfen                 # noqa: E402
from plan.engine import Engine                             # noqa: E402
from plan.certify import certify                           # noqa: E402
from plan.planner import Planner, PlannerError, Repetition  # noqa: E402


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=20)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--verbose", action="store_true")
    ap.add_argument("--sfen", help="plan one given target SFEN instead of sampling")
    ap.add_argument("--retries", type=int, default=5, help="planner restarts with new seeds")
    args = ap.parse_args()
    targets = []
    if args.sfen:
        from count.sfen import parse
        targets = [parse(args.sfen)[0]]
    else:
        t0 = time.time()
        s = Sampler(chu_setup("file", **PRIMARY), "file", True)
        rng = random.Random(args.seed)
        targets = [s.sample(rng)[0] for _ in range(args.n)]
        print(f"sampled {args.n} targets in {time.time() - t0:.0f}s")
    outcomes = Counter()
    plies = []
    for i, T in enumerate(targets):
        t0 = time.time()
        last = None
        for attempt in range(args.retries):
            pl = Planner(T, Engine(), verbose=args.verbose, seed=attempt)
            try:
                moves = pl.run()
            except PlannerError as e:
                last = f"{e.phase}: {e.reason}"
                continue
            except Repetition as e:
                last = f"REPETITION {e}"
                continue
            except Exception as e:                        # planner bug
                last = f"EXCEPTION {type(e).__name__}: {e}"
                if args.verbose:
                    traceback.print_exc()
                continue
            ok, why = certify(moves, T)
            if ok:
                outcomes["ok"] += 1
                plies.append(len(moves))
                print(f"[{i}] ok  {len(moves)} plies  attempt {attempt}  {time.time() - t0:.1f}s")
                break
            last = f"CERTIFY: {why}"
        else:
            outcomes[last.split(":")[0]] += 1
            print(f"[{i}] FAIL after {args.retries} attempts: {last}  ({time.time() - t0:.1f}s)")
            if args.verbose:
                print("   target:", to_sfen(T))
    print("summary:", dict(outcomes), "mean plies", sum(plies) / len(plies) if plies else None,
          "max plies", max(plies) if plies else None)


if __name__ == "__main__":
    main()
