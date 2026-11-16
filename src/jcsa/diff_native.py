#!/usr/bin/env python3
"""Test 2: random candidate positions, legal-move sets of the native JCSA engine vs our
layer (src/jcsa/mode.py on the pinned engine), without a flag and under a random
counter-strike square; plus the native engine's lishogi mode vs the pinned engine.
Usage: python3 src/jcsa/diff_native.py --n 1000000 --seed 41 --procs 14 --out out/runs/diff_native_seed41"""
import argparse, json, random, sys, time
from collections import Counter
from multiprocessing import Pool
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
_c = {}


def _init():
    from count.candidates import PRIMARY, chu_setup
    from count.sampler import Sampler
    from plan.engine import Engine
    from jcsa.native import NativeEngine
    _c["S"] = Sampler(chu_setup("file", **PRIMARY), "file", True)
    _c["old"] = Engine()
    _c["nj"] = NativeEngine("jcsa")
    _c["nl"] = NativeEngine("lishogi")


def _work(args):
    from count.sampler import to_sfen
    from jcsa.mode import legal_moves
    from plan.moves import SQUARES, usi_sq
    seed, n = args
    rng = random.Random(seed)
    c = Counter()
    dis = []
    for _ in range(n):
        b = _c["S"].sample(rng)[0]
        if not any(p == ("B", "K") for p in b.values()):
            continue
        cand = [q for q in SQUARES if b.get(q, ("W",))[0] == "W"]      # empty or White-held squares
        for flag in (None, rng.choice(cand)):
            sfen = to_sfen(b, "b", usi_sq(flag) if flag else "-")
            c["positions"] += 1
            if flag:
                c["with flag"] += 1
            lay = legal_moves(_c["old"], b, "B", flag)
            _c["nj"].position(sfen)
            nj = _c["nj"].legal()
            if lay != nj:
                c["JCSA move-set disagreements"] += 1
                if len(dis) < 50:
                    dis.append({"kind": "jcsa", "sfen": sfen, "layer_only": sorted(lay - nj)[:6], "native_only": sorted(nj - lay)[:6]})
            if flag:
                _c["old"].position(sfen)
                ol = _c["old"].legal()
                _c["nl"].position(sfen)
                nl = _c["nl"].legal()
                if ol != nl:
                    c["lishogi move-set disagreements (new vs pinned engine)"] += 1
                    if len(dis) < 50:
                        dis.append({"kind": "lishogi", "sfen": sfen, "pinned_only": sorted(ol - nl)[:6], "native_only": sorted(nl - ol)[:6]})
                if lay != ol:
                    c["positions where the ban changes the legal set"] += 1
    return c, dis


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=10000)
    ap.add_argument("--seed", type=int, default=41)
    ap.add_argument("--procs", type=int, default=14)
    ap.add_argument("--out", required=True)
    a = ap.parse_args()
    chunks = max(a.procs * 4, a.n // 5000)
    per = a.n // chunks
    tot = Counter()
    alld = []
    t0 = time.time()
    with Pool(a.procs, initializer=_init) as pool:
        for i, (c, dis) in enumerate(pool.imap_unordered(_work, [(a.seed * 10007 + i, per) for i in range(chunks)])):
            tot.update(c)
            alld += dis
            if (i + 1) % 20 == 0:
                print(f"  ... {tot['positions']} positions, {dict(tot)} {time.time() - t0:.0f}s", flush=True)
    json.dump(alld, open(a.out + "_disagreements.json", "w"), indent=1)
    print(f"done: {dict(tot)}; {time.time() - t0:.0f}s; disagreements saved: {len(alld)}")


if __name__ == "__main__":
    main()
