#!/usr/bin/env python3
"""Differential test of chu-plan's D13 mate check (src/plan/cpp/mate.cpp) against
jcsa/mode.py mated(), under both move-rule sets: lishogi (Python with plan.engine.Engine,
as endings_share / reverify / mate_ending use it) and JCSA (Python with the native engine's
`rules jcsa`, the rule set D13 prescribes).

--boards N: N uniform candidate boards (PRIMARY setup), each with Black and with White to move,
no flag.  --flagged N: the first N flag-stratum boards (flags, flagsj) of --records with their
counter-strike flag, where the two rule sets can differ.  --games K: K regenerated M-E certificate games; every position with a flag and every
--every-th other position is compared, and on the first --full games the whole list of mated
plies from chu-plan's `mates` is compared with Python's replay_jcsa(count_mates=True) (JCSA).

Both sides apply D13a (a promotion to a prince is an escape) and D13b (a capture of the
opponent's last royal is an escape); with CHU_PLAN_D13_ORIGINAL=1 in the environment both use
D13 as first worded (pilot P1), with CHU_PLAN_D13_READING_A=1 both omit D13b (P2, P3, run G13).
The Python references use CHU_ENGINE / CHU_ENGINE_JCSA, by default out/engine/chushogi-gen
(v0.2.1, the runs' engine, as chu-plan's chushogi/src); v0.2.0-rc1 (.engines/chushogi-jcsa)
predates the promoted-kirin capture-square fix and differs on 4 of the 2000 flagged boards.

Usage: python3 tests/test_cmate.py [--boards 2000] [--flagged 2000] [--games 40] [--full 4] [--every 25]
       [--certs out/runs/estimate_seed191_40000_1000_600_1000j_certs.jsonl.gz]
       [--records out/runs/estimate_seed191_40000_1000_600_1000j.jsonl] [--procs 2] [--seed 61]
"""
import argparse
import gzip
import json
import os
import random
import sys
from multiprocessing import Pool
from pathlib import Path

_ROOT = Path(__file__).resolve().parent.parent
for _v in ("CHU_ENGINE", "CHU_ENGINE_JCSA"):
    os.environ.setdefault(_v, str(_ROOT / "out" / "engine" / "chushogi-gen"))
sys.path.insert(0, str(_ROOT / "src"))
_c = {}


def _init(boards):
    from jcsa.native import NativeEngine
    from plan.cplanner import CPlan
    from plan.engine import Engine
    _c["cp"], _c["eng"], _c["nl"], _c["nj"] = CPlan(), Engine(), Engine(), NativeEngine("jcsa")
    if boards:
        from count.candidates import PRIMARY, chu_setup
        from count.sampler import Sampler
        _c["S"] = Sampler(chu_setup("file", **PRIMARY), "file", True)


def _cmp(board, turn, flag):
    """[lishogi same, jcsa same, py lishogi, py jcsa]"""
    from jcsa.mode import mated
    pe = os.environ.get("CHU_PLAN_D13_ORIGINAL") is None          # D13a unless chu-plan runs D13 as first worded
    ce = os.environ.get("CHU_PLAN_D13_READING_A") is None         # D13b unless chu-plan runs reading (a)
    pl, pj = mated(_c["nl"], board, turn, flag, pe, ce), mated(_c["nj"], board, turn, flag, pe, ce)
    cl, cj = _c["cp"].mated(board, turn, flag, "lishogi"), _c["cp"].mated(board, turn, flag, "jcsa")
    return [pl == cl, pj == cj, pl, pj]


def _work_boards(seed):
    board = _c["S"].sample(random.Random(seed))[0]
    return [[seed, t, None] + _cmp(board, t, None) for t in "BW"]


def _work_flagged(rec):
    from count.sfen import parse
    board, flag = parse(rec["sfen"])[0], tuple(rec["flag"])
    return [rec["seed"], "B", flag] + _cmp(board, "B", flag)


def _work_cand(rec):
    """chu-plan `cand` vs is_candidate on the geometric one-ply predecessors (both movers,
    un-captures included: mostly non-candidates) of a record's board."""
    from count.candidates import chu_setup, is_candidate
    from count.sfen import parse
    from jcsa import mate_ending
    from jcsa.mate_ending import predecessors
    if mate_ending._SETUP is None:                  # workers are not forked (3.14: forkserver)
        mate_ending._init(sampler=False)
    setup = chu_setup("file", identify_royals=True, mover_royal_required=False)
    T = parse(rec["sfen"])[0]
    n, pos, diff = 0, 0, []
    for mover in "WB":
        for k, (P, _) in enumerate(predecessors(T, mover)):
            if k % 7:
                continue
            py = is_candidate(setup, P, "file", True)
            n += 1
            pos += py
            if py != _c["cp"].cand(P):
                diff.append(rec["seed"])
    return n, pos, diff


def _work_game(job):
    from count.sfen import INITIAL, parse
    from jcsa.mode import replay_jcsa
    i, moves, every, full = job
    out, eng = [], _c["eng"]
    eng.position(INITIAL)
    for k, mv in enumerate(moves + [None]):
        board, turn, flag = parse(eng.sfen())
        if flag is not None or k % every == 0:
            out.append([i, k, flag is not None] + _cmp(board, turn, flag))
        if mv:
            eng.move(mv)
    if full:
        py = replay_jcsa(moves, _c["eng"], _c["nj"], count_mates=True,
                         prince_escape=os.environ.get("CHU_PLAN_D13_ORIGINAL") is None,
                         capture_escape=os.environ.get("CHU_PLAN_D13_READING_A") is None)[4]
        c = [k for k in _c["cp"].mates(moves) if k < len(moves) - 1]    # replay_jcsa skips the last
        out.append([i, "full", py == c, len(py), len(c)])
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--boards", type=int, default=2000)
    ap.add_argument("--flagged", type=int, default=0)
    ap.add_argument("--records", help="records generated by estimate.py; required with --flagged or --cand")
    ap.add_argument("--games", type=int, default=0)
    ap.add_argument("--full", type=int, default=4)
    ap.add_argument("--every", type=int, default=25)
    ap.add_argument("--certs", help="generated certificate archive; required with --games")
    ap.add_argument("--procs", type=int, default=2)
    ap.add_argument("--seed", type=int, default=61)
    ap.add_argument("--cand", type=int, default=0, help="records whose predecessors test chu-plan cand")
    a = ap.parse_args()
    if (a.flagged or a.cand) and not a.records:
        ap.error("--records is required with --flagged or --cand")
    if a.games and not a.certs:
        ap.error("--certs is required with --games")
    bad = 0
    with Pool(a.procs, initializer=_init, initargs=(a.boards > 0,)) as pool:
        if a.boards:
            rows = [r for rs in pool.imap_unordered(_work_boards, range(a.seed * 100000, a.seed * 100000 + a.boards))
                    for r in rs]
            for name, col, py in (("lishogi", 3, 5), ("jcsa", 4, 6)):
                diff = [r for r in rows if not r[col]]
                bad += len(diff)
                print(f"boards ({name} rules): {len(rows)} positions, mated (Python) {sum(r[py] for r in rows)}, "
                      f"differ {len(diff)} {diff[:5]}")
            print(f"  lishogi vs JCSA verdicts differ on {sum(r[5] != r[6] for r in rows)} positions")
        if a.cand:
            recs = [r for r in map(json.loads, open(a.records)) if r["stratum"] == "nonterm"][:a.cand]
            res = list(pool.imap_unordered(_work_cand, recs))
            diff = [d for _, _, ds in res for d in ds]
            bad += len(diff)
            print(f"cand: {sum(n for n, _, _ in res)} predecessor boards, candidates (Python) "
                  f"{sum(p for _, p, _ in res)}, differ {len(diff)} {diff[:5]}")
        if a.flagged:
            recs = [r for r in map(json.loads, open(a.records)) if r["stratum"] in ("flags", "flagsj")][:a.flagged]
            rows = list(pool.imap_unordered(_work_flagged, recs))
            for name, col, py in (("lishogi", 3, 5), ("jcsa", 4, 6)):
                diff = [r for r in rows if not r[col]]
                bad += len(diff)
                print(f"flagged boards ({name} rules): {len(rows)} positions, mated (Python) {sum(r[py] for r in rows)}, "
                      f"differ {len(diff)} {diff[:5]}")
            print(f"  lishogi vs JCSA verdicts differ on {sum(r[5] != r[6] for r in rows)} positions "
                  f"{[r[:3] + r[5:] for r in rows if r[5] != r[6]][:5]}")
        if a.games:
            jobs = []
            with gzip.open(a.certs, "rt") as fh:
                for i, line in enumerate(fh):
                    if i >= a.games:
                        break
                    jobs.append((i, json.loads(line)["moves"], a.every, i < a.full))
            rows = [r for rs in pool.imap_unordered(_work_game, jobs) for r in rs]
            pos = [r for r in rows if r[1] != "full"]
            for name, col, py in (("lishogi", 3, 5), ("jcsa", 4, 6)):
                diff = [r for r in pos if not r[col]]
                bad += len(diff)
                print(f"games ({name} rules): {len(pos)} positions ({sum(r[2] for r in pos)} with a flag), mated "
                      f"(Python) {sum(r[py] for r in pos)}, differ {len(diff)} {diff[:5]}")
            print(f"  lishogi vs JCSA verdicts differ on {sum(r[5] != r[6] for r in pos)} positions "
                  f"({sum(r[5] != r[6] for r in pos if r[2])} with a flag)")
            full = [r for r in rows if r[1] == "full"]
            bad += sum(not r[2] for r in full)
            print(f"full mate lists (JCSA): {sum(r[2] for r in full)} / {len(full)} games identical; "
                  f"mated plies per game {[r[3] for r in full]}")
    print("OK" if bad == 0 else f"FAIL ({bad})")
    sys.exit(bad > 0)


if __name__ == "__main__":
    main()
