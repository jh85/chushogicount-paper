#!/usr/bin/env python3
"""Validation of the C++ variant engine (src/variant/cpp) against the Python one.

For each variant (V1, V8, V6):
  1. random play from the start in Python collects N distinct reachable states
     (board, turn, raw flag), terminal ones included; the C++ oracle is asked
     about the same states: legal-move sets, game status, the candidate test
     (bfs2's rotated board), the I10 lane check and the pack/unpack round trip
     must agree, and the C++ board index must be injective on the sample;
  2. the same comparison on N random boards (random subset of the pieces on
     random squares, random side to move and flag), which exercises the
     candidate test on non-candidates and the move generator on positions
     random play rarely reaches;
  3. an independent depth-limited BFS in Python (states keyed as in bfs2.py)
     is compared with `bfs NAME --depth D`: states per level and every
     statistic line must be identical;
  4. optionally (--limit N) `python3 src/variant/bfs2.py NAME --limit N` is
     compared line by line with `bfs NAME --limit N` (same BFS order).

Usage: python3 tests/test_variant_cpp.py [--n 20000] [--seed 1] [--depth 6] [--limit 0]
                                         [--variants V1,V8,V6]
Build first: make -C src/variant/cpp
"""
import argparse
import random
import re
import subprocess
import sys
import time
from collections import Counter, deque
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "src"))
from count.candidates import is_candidate                   # noqa: E402
from plan.lanes import Geometry, lane_ok                     # noqa: E402
from variant.bfs import variants                             # noqa: E402

CPP = ROOT / "out" / "variant"


def rotate(setup, bd):
    nf, nr = setup.nfiles, setup.nranks
    return {(nf - 1 - x, nr + 1 - r): ("W" if c == "B" else "B", role) for (x, r), (c, role) in bd.items()}


def oriented(var, setup, st):
    bd = var.to_board_dict(st[0])
    return rotate(setup, bd) if st[1] == "W" else bd


def py_answer(var, setup, colour, geo, st):
    moves = {(i, -1 if m is None else m, j, int(p)) for i, m, j, p in var.legal_moves(st)}
    bd = oriented(var, setup, st)
    return var.status(st), moves, int(is_candidate(setup, bd, "file", colour)), int(lane_ok(bd, geo))


def ask_oracle(name, states, var):
    lines = []
    for board, turn, flag in states:
        lines.append(" ".join(str(c) for c in board) + f" {turn} {'-' if flag is None else flag}")
    p = subprocess.run([str(CPP / "oracle"), name], input="\n".join(lines) + "\n", capture_output=True, text=True)
    if p.returncode != 0:
        sys.exit(f"oracle failed: {p.stderr}")
    out = []
    for line in p.stdout.splitlines():
        t = line.split()
        assert t[0] == "status" and t[2] == "moves"
        k = int(t[3])
        moves = {tuple(int(v) for v in m.split(",")) for m in t[4:4 + k]}
        rest = t[4 + k:]
        d = {rest[i]: rest[i + 1] for i in range(0, len(rest), 2)}
        assert "PACK-MISMATCH" not in line, line
        out.append((t[1], moves, int(d["cand"]), int(d["lane"]), d["index"]))
    assert len(out) == len(states)
    return out


def compare(name, label, var, setup, colour, geo, states):
    cpp = ask_oracle(name, states, var)
    bad = 0
    index_of = {}
    for st, (c_status, c_moves, c_cand, c_lane, c_index) in zip(states, cpp):
        p_status, p_moves, p_cand, p_lane = py_answer(var, setup, colour, geo, st)
        if (p_status, p_moves, p_cand, p_lane) != (c_status, c_moves, c_cand, c_lane):
            bad += 1
            if bad <= 5:
                print(f"  DISAGREEMENT on {sorted(var.to_board_dict(st[0]).items())} {st[1]} flag={st[2]}")
                print(f"    python: {p_status} cand={p_cand} lane={p_lane} moves={sorted(p_moves)}")
                print(f"    c++:    {c_status} cand={c_cand} lane={c_lane} moves={sorted(c_moves)}")
        if c_index != "-":
            prev = index_of.setdefault(c_index, st[0])
            if prev != st[0]:
                bad += 1
                print(f"  INDEX COLLISION {c_index}: {prev} vs {st[0]}")
        elif c_cand:
            bad += 1
            print(f"  candidate without index: {st}")
    n_cand = sum(c[2] for c in cpp)
    n_term = sum(c[0] != "playing" for c in cpp)
    n_flag = sum(st[2] is not None for st in states)
    print(f"  {label}: {len(states)} states compared, {bad} disagreements"
          f" (candidates {n_cand}, terminal {n_term}, flagged {n_flag})")
    return bad


def random_play_states(var, n, rng, max_plies=300):
    seen = {}
    while len(seen) < n:
        st = var.start
        for _ in range(max_plies):
            seen.setdefault(st, None)
            if len(seen) >= n:
                break
            if var.status(st) != "playing":
                break
            mv = rng.choice(var.legal_moves(st))
            st = var.apply(st, mv)
    return list(seen)


def random_boards(var, n, rng):
    out = []
    while len(out) < n:
        board = [0] * var.n
        pieces = list(range(1, len(var.pieces) + 1))
        rng.shuffle(pieces)
        k = rng.randint(2, min(8, len(pieces)))
        squares = rng.sample(range(var.n), k)
        for code, sq in zip(pieces[:k], squares):
            board[sq] = code
        turn = rng.choice("BW")
        occupied = [i for i in range(var.n) if board[i]]
        flag = rng.choice([None, None, rng.choice(occupied)])
        out.append((tuple(board), turn, flag))
    return out


def py_bfs(var, setup, colour, geo, depth):
    """Depth-limited BFS with bfs2.py's bookkeeping (states keyed by raw flag)."""
    def visit(st, seen, stats):
        bd = oriented(var, setup, st)
        if not is_candidate(setup, bd, "file", colour):
            stats["violations"] += 1
            return False
        if st in seen:
            return False
        seen.add(st)
        if st[2] is None:
            if not lane_ok(bd, geo):
                stats["i10"] += 1
            if st[1] == "B":
                stats["boards_b"].add(st[0])
        elif st[1] == "B":
            stats["boards_b_flag"].add(st[0])
        return True

    stats = Counter()
    stats["boards_b"], stats["boards_b_flag"] = set(), set()
    seen = set()
    visit(var.start, seen, stats)
    level = [var.start]
    per_level = [1]
    popped = Counter()
    for d in range(depth + 1):
        nxt = []
        for st in level:
            status = var.status(st)
            board, turn, flag = st
            if turn == "B":
                popped[("B", status != "playing")] += 1
                popped[status] += 1
                if flag is None:
                    popped["flag-none"] += 1
                else:
                    a, b = set(var.legal_moves(st)), set(var.legal_moves((board, turn, None)))
                    popped["flag-effective" if a != b else "flag-ineffective"] += 1
            else:
                popped[("W", status != "playing")] += 1
            if status != "playing":
                popped["terminal"] += 1
                continue
            if d == depth:
                continue
            for mv in var.legal_moves(st):
                q = var.apply(st, mv)
                if visit(q, seen, stats):
                    nxt.append(q)
        if d < depth:
            per_level.append(len(nxt))
        level = nxt
    only_flag = len(stats["boards_b_flag"] - stats["boards_b"])
    return {
        "states": len(seen),
        "black": (popped[("B", False)], popped[("B", True)], popped["royalslost"], popped["bareking"],
                  popped["stalemate"], popped["draw"], popped[("W", False)] + popped[("W", True)]),
        "flags": (popped["flag-none"], popped["flag-effective"], popped["flag-ineffective"]),
        "boards_b": len(stats["boards_b"]),
        "violations": (stats["violations"], stats["i10"]),
        "only_flag": only_flag,
        "popped": (sum(popped[k] for k in popped if isinstance(k, tuple)), popped["terminal"]),
        "levels": per_level,
    }


def parse_cpp_output(text):
    """The statistic lines of bfs (and bfs2.py) as tuples of integers."""
    out = {}
    for line in text.splitlines():
        ints = [int(v) for v in re.findall(r"(?<![\w.])\d+(?![\d.]*[.])", line)]
        if " reachable states in " in line:
            out["states"] = ints[0]
        elif line.startswith("  Black to move:"):
            out["black"] = tuple(ints)
        elif line.startswith("  Black-to-move states by flag:"):
            out["flags"] = tuple(ints)
        elif line.startswith("  reachable Black-to-move boards"):
            out["boards_b"] = ints[0]
            out["C"] = ints[1]
        elif line.startswith("  superset violations"):
            out["violations"] = tuple(ints)
        elif line.startswith("  Black-to-move boards reachable only with a flag:"):
            out["only_flag"] = ints[0]
            out["popped"] = (ints[1], ints[2])
        elif line.startswith("  states per level:"):
            out["levels"] = [int(v.split(":")[1]) for v in line.split()[3:]]
    return out


def run_cpp(name, *args):
    p = subprocess.run([str(CPP / "bfs"), name, *args], capture_output=True, text=True)
    if p.returncode != 0:
        sys.exit(f"bfs failed: {p.stderr}")
    return p.stdout


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=20000)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--depth", type=int, default=6)
    ap.add_argument("--limit", type=int, default=0, help="also compare with bfs2.py --limit N (slow)")
    ap.add_argument("--variants", default="V1,V8,V6")
    a = ap.parse_args()
    for exe in ("oracle", "bfs"):
        if not (CPP / exe).exists():
            sys.exit(f"{CPP / exe} missing; build with `make -C src/variant/cpp`")
    total_bad = 0
    for name in a.variants.split(","):
        var, setup, colour = variants()[name]
        geo = Geometry(setup)
        rng = random.Random(a.seed)
        print(f"{name}:")
        t0 = time.time()
        states = random_play_states(var, a.n, rng)
        total_bad += compare(name, "random play", var, setup, colour, geo, states)
        boards = random_boards(var, a.n, rng)
        total_bad += compare(name, "random boards", var, setup, colour, geo, boards)
        print(f"  ({time.time() - t0:.0f}s)")
        t0 = time.time()
        py = py_bfs(var, setup, colour, geo, a.depth)
        cpp = parse_cpp_output(run_cpp(name, "--depth", str(a.depth)))
        for key in ("states", "black", "flags", "boards_b", "violations", "only_flag", "popped", "levels"):
            if py[key] != cpp.get(key):
                total_bad += 1
                print(f"  DEPTH-{a.depth} BFS MISMATCH {key}: python {py[key]} c++ {cpp.get(key)}")
        print(f"  depth-{a.depth} BFS: {py['states']} states, levels {py['levels']}, "
              f"{'identical' if py == {k: cpp.get(k) for k in py} else 'DIFFERENT'} ({time.time() - t0:.0f}s)")
        if a.limit:
            t0 = time.time()
            p = subprocess.run([sys.executable, str(ROOT / "src" / "variant" / "bfs2.py"), name, "--limit", str(a.limit)],
                               capture_output=True, text=True)
            if p.returncode != 0:
                sys.exit(f"bfs2.py failed: {p.stderr}")
            ref = parse_cpp_output(p.stdout)
            cpp = parse_cpp_output(run_cpp(name, "--limit", str(a.limit)))
            keys = ("states", "black", "flags", "boards_b", "C", "violations")
            same = all(ref.get(k) == cpp.get(k) for k in keys)
            for k in keys:
                if ref.get(k) != cpp.get(k):
                    print(f"  LIMIT-{a.limit} MISMATCH {k}: bfs2.py {ref.get(k)} c++ {cpp.get(k)}")
            total_bad += 0 if same else 1
            print(f"  limit-{a.limit} vs bfs2.py: {ref.get('black')} {'identical' if same else 'DIFFERENT'} ({time.time() - t0:.0f}s)")
    print("PASS" if total_bad == 0 else f"FAIL ({total_bad} problems)")
    sys.exit(0 if total_bad == 0 else 1)


if __name__ == "__main__":
    main()
