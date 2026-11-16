#!/usr/bin/env python3
"""Cross-validation of the realizable-flags predicate on the validation variants
(docs/variant-cpp.md, "Flag states"): the Python predicate
plan.flags.realizable_flags(board, setup=...) and the C++ one
(src/variant/cpp/flags.cpp, through `flagcheck NAME xval`) must accept the
same flag squares, with and without the I10 lane check of the predecessor.

Boards: uniform candidates of the variant (count.sampler.Sampler) and
Black-to-move boards reached by random play in Python.

Usage: python3 tests/test_variant_flags.py [--n 2000] [--seed 1] [--procs 4] [--variants V1,V8,V6]
                                           [--full]
--n is the number of uniform candidates per variant (plus n/2 reachable boards);
--full also runs `flagcheck NAME full` on out/runs/bfs_cpp_NAME_flagged.bin when
that dump of a complete search exists (slow: minutes with 14 threads).
Build first: make -C src/variant/cpp
"""
import argparse
import random
import subprocess
import sys
import time
from multiprocessing import Pool
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "src"))
from count.sampler import Sampler                           # noqa: E402
from plan.flags import realizable_flags                     # noqa: E402
from variant.bfs import variants                            # noqa: E402

CPP = ROOT / "out" / "variant"
_V = {}


def _init(name):
    _V["v"] = variants()[name]


def _py(bd):
    var, setup, colour = _V["v"]
    with_l = {var.idx(*sq) for sq in realizable_flags(bd, setup=setup, colour=colour, lanes=True)}
    no_l = {var.idx(*sq) for sq in realizable_flags(bd, setup=setup, colour=colour, lanes=False)}
    return with_l, no_l


def boards_for(name, n, seed):
    var, setup, colour = variants()[name]
    rng = random.Random(seed)
    s = Sampler(setup, "file", colour)
    out = [s.sample(rng)[0] for _ in range(n)]
    reach = {}
    while len(reach) < n // 2:
        st = var.start
        for _ in range(300):
            if st[1] == "B":
                reach.setdefault(st[0], None)
            if var.status(st) != "playing" or len(reach) >= n // 2:
                break
            st = var.apply(st, rng.choice(var.legal_moves(st)))
    out += [var.to_board_dict(b) for b in reach]
    return out


def codes(var, bd):
    board = [0] * var.n
    for sq, p in bd.items():
        board[var.idx(*sq)] = var.code[p]
    return board


def cpp_answers(name, var, boards):
    text = "\n".join(" ".join(str(c) for c in codes(var, bd)) for bd in boards) + "\n"
    p = subprocess.run([str(CPP / "flagcheck"), name, "xval"], input=text, capture_output=True, text=True)
    if p.returncode != 0:
        sys.exit(f"flagcheck failed: {p.stderr}")
    out = []
    for line in p.stdout.splitlines():
        a, b = line.split(";")
        out.append(({int(v) for v in a.split()[1:]}, {int(v) for v in b.split()[1:]}))
    assert len(out) == len(boards)
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=2000)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--procs", type=int, default=4)
    ap.add_argument("--variants", default="V1,V8,V6")
    ap.add_argument("--full", action="store_true")
    a = ap.parse_args()
    if not (CPP / "flagcheck").exists():
        sys.exit("build first: make -C src/variant/cpp")
    bad = 0
    for name in a.variants.split(","):
        var, setup, colour = variants()[name]
        t0 = time.time()
        boards = boards_for(name, a.n, a.seed)
        cpp = cpp_answers(name, var, boards)
        with Pool(a.procs, initializer=_init, initargs=(name,)) as pool:
            py = pool.map(_py, boards, chunksize=64)
        mism = 0
        with_flags = sum(1 for w, _ in py if w)
        accepted = sum(len(w) for w, _ in py)
        extra_nolane = sum(len(nl) - len(w) for w, nl in py)
        for bd, (pw, pn), (cw, cn) in zip(boards, py, cpp):
            if (pw, pn) != (cw, cn):
                mism += 1
                if mism <= 5:
                    print(f"  MISMATCH {sorted(bd.items())}: python {sorted(pw)}/{sorted(pn)} c++ {sorted(cw)}/{sorted(cn)}")
        bad += mism
        print(f"{name}: {len(boards)} boards ({a.n} uniform candidates + {len(boards) - a.n} reachable), "
              f"{mism} mismatches; boards with accepted flags {with_flags}, accepted flag states {accepted}, "
              f"accepted only without the lane check {extra_nolane} ({time.time() - t0:.0f}s)")
        dump = ROOT / "runs" / f"bfs_cpp_{name}_flagged.bin"
        if a.full and dump.exists():
            t0 = time.time()
            p = subprocess.run([str(CPP / "flagcheck"), name, "full", "--flagged", str(dump), "--threads", str(a.procs)],
                               capture_output=True, text=True)
            print(p.stdout.rstrip())
            print(f"  (flagcheck full: {time.time() - t0:.0f}s)")
            if p.returncode != 0 or "FAIL" in p.stdout:
                bad += 1
    print("PASS" if bad == 0 else f"FAIL ({bad})")
    sys.exit(0 if bad == 0 else 1)


if __name__ == "__main__":
    main()
