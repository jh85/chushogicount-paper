"""Python interface to chu-plan (src/plan/cpp), the C++ port of plan/planner.py and
plan/relax.py.  Same calls, same results (tests/test_cplanner.py checks game-for-game
equality with the Python planner); the games are still untrusted and are certified by
plan/certify.py with the engine binary as before.

    cp = CPlan()
    moves = cp.plan(T, seed=0, end_turn="B", strategy=None, defer=False, park=False)
        # = Planner(T, eng, seed=seed, end_turn=..., strategy=..., defer=..., park=...).run()
        # raises plan.planner.PlannerError / Repetition, or CPlanError for any other
        # exception the Python planner would raise (type name and message kept)
    moves, info = cp.relax(T, depth=..., beam=..., tries=..., planner_retries=..., turn="B")
        # = relax(T, eng, ..., compact_seen=True, fix_turn=False)
    cp.mated(board, turn, flag)   # D13 mate under JCSA move rules (rules="lishogi": = jcsa.mode.mated(Engine(), ...))
    cp.mates(moves)               # plies (0..len) whose position has the side to move mated
"""
import os
import subprocess
import sys
from pathlib import Path

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from plan.planner import PlannerError, Repetition     # noqa: E402

DEFAULT = os.environ.get("CHU_PLAN", str(Path(__file__).resolve().parents[2] / "out" / "bin" / "chu-plan"))


class CPlanError(Exception):
    """An exception other than PlannerError / Repetition in the planner (e.g. KeyError)."""
    def __init__(self, typ, msg):
        super().__init__(msg)
        self.typ = typ


def _target(T):
    return f"{len(T)} " + " ".join(f"{x * 12 + r - 1}:{c}:{role}" for (x, r), (c, role) in T.items())


def _sq(i):
    return (i // 12, i % 12 + 1)


class CPlan:
    def __init__(self, path=DEFAULT):
        self.p = subprocess.Popen([path], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)

    def ask(self, cmd):
        self.p.stdin.write(cmd + "\n")
        self.p.stdin.flush()
        out = self.p.stdout.readline()
        if not out:
            raise RuntimeError(f"chu-plan died on: {cmd[:120]}")
        return out.rstrip("\n")

    def plan(self, T, seed=0, end_turn="B", strategy=None, defer=False, park=False):
        strategy = strategy or ("greedy" if seed % 2 == 0 else "peel")
        r = self.ask(f"plan {seed} {strategy} {int(defer)} {int(park)} {end_turn} {_target(T)}")
        kind, _, rest = r.partition(" ") if r.startswith("ok") else r.partition("\t")
        if kind == "ok":
            return rest.split()
        if kind == "PlannerError":
            at, phase, reason = rest.split("\t", 2)
            e = PlannerError(phase, reason, None if at == "-" else _sq(int(at)))
            raise e
        if kind == "Repetition":
            raise Repetition(rest)
        if kind == "Exception":
            typ, msg = rest.split("\t", 1)
            raise CPlanError(typ, msg)
        raise RuntimeError(r)

    def relax(self, T, depth=10, beam=12, tries=4, planner_retries=2, turn="B", compact_seen=True, log=None,
              fix_turn=False):
        r = self.ask(f"relax {depth} {beam} {tries} {planner_retries} {turn} {int(fix_turn)} {_target(T)}").split()
        if r[0] == "ok":
            tried, levels, retracted, base, score = map(int, r[1:6])
            info = {"tried": tried, "levels": levels, "ok": True, "retracted": retracted,
                    "plies": len(r) - 6, "score": (base, score)}
            if log:
                log(f"relax: rescued after {retracted} retractions, score {base}->{score}")
            return r[6:], info
        if r[0] == "none":
            return None, {"tried": int(r[1]), "levels": int(r[2]), "ok": False}
        raise RuntimeError(" ".join(r))

    def certify(self, moves, T, turn="B"):
        r = self.ask(f"certify {turn} {_target(T)} {len(moves)} {' '.join(moves)}")
        return r.startswith("ok"), r.partition(" ")[2]

    def cand(self, board):
        """count/candidates.py is_candidate(PRIMARY setup, "file", colour) in chu-plan."""
        r = self.ask(f"cand {_target(board)}")
        if r not in ("0", "1"):
            raise RuntimeError(r)
        return r == "1"

    def mated(self, board, turn="B", flag=None, rules="jcsa"):
        fl = "-" if flag is None else str(flag[0] * 12 + flag[1] - 1)
        r = self.ask(f"mated {rules} {turn} {fl} {_target(board)}")
        if r not in ("0", "1"):
            raise RuntimeError(r)
        return r == "1"

    def fixpairs(self, board, turn, flag, mv, steps_a, steps_b, k=16):
        """mate.h fix_pairs: up to k index pairs (i, j), in order, steps_a[i] a move of the side
        to move and steps_b[i][j] a reply, with every state safe (MatePlanner.safe without the
        final-target exception) after steps_a[i], steps_b[i][j] and mv."""
        fl = "-" if flag is None else str(flag[0] * 12 + flag[1] - 1)
        r = self.ask(f"fixpair {turn} {fl} {mv} {k} {len(steps_a)} {' '.join(steps_a)} "
                     + " ".join(f"{len(b)} {' '.join(b)}" for b in steps_b) + f" {_target(board)}").split()
        if r[0] != "ok":
            raise RuntimeError(" ".join(r))
        return [tuple(map(int, x.split(","))) for x in r[1:]]

    def mates(self, moves):
        """Indices i of the positions before move i (i = len(moves): the final position) in
        which the side to move is mated (D13), replayed under JCSA move rules.  Raises
        ValueError(i) if move i is not JCSA-legal."""
        r = self.ask(f"mates {len(moves)} {' '.join(moves)}").split()
        if r[0] == "illegal":
            raise ValueError(int(r[1]))
        if r[0] != "ok":
            raise RuntimeError(" ".join(r))
        return [int(x) for x in r[1:]]
