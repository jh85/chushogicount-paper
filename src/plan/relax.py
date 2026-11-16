"""Retro-relaxation fallback for planner failures (Eii, plan item 2).

From a target the planner cannot solve, search backward with non-capturing,
non-promoting retractions only (pawns and lances step backward too), colours
alternating, for a predecessor the planner can solve.  A candidate predecessor
is kept only if the engine lists the forward move as legal, the position is a
candidate (static filter) and non-terminal.  Beam search guided by a pocket
score (pieces whose square can only be entered through a small region).

Certificate = planner game to the predecessor + the retracted moves forward,
replayed through the engine as usual (certify.py).
"""
import hashlib
import sys
from pathlib import Path

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from count.candidates import PRIMARY, chu_setup, is_candidate     # noqa: E402
from count.sampler import to_sfen                                 # noqa: E402
from plan.certify import certify                                   # noqa: E402
from plan.engine import Engine                                     # noqa: E402
from plan.moves import SQUARES, reverse_moves, usi                 # noqa: E402
from plan.planner import WALLS, Planner, PlannerError, Repetition  # noqa: E402

SETUP = chu_setup("file", **PRIMARY)


def pocket_score(board):
    """Sum over movable pieces of (12 - size of the region from which the
    piece's square can be entered, through empty squares, others fixed)+."""
    score = 0
    for sq, piece in board.items():
        if piece[1] in WALLS:
            continue
        b = dict(board)
        del b[sq]
        region, stack = {sq}, [sq]
        while stack and len(region) < 12:
            cur = stack.pop()
            for t in reverse_moves(b, cur, piece):
                if t not in region:
                    region.add(t)
                    stack.append(t)
        score += 12 - len(region)
    return score


def predecessors(board, turn, eng):
    """Non-capturing, non-promoting retractions of the side that just moved.
    Yields (predecessor board, forward usi move)."""
    mover = "W" if turn == "B" else "B"
    for sq, piece in list(board.items()):
        if piece[0] != mover:
            continue
        b = dict(board)
        del b[sq]
        for a in reverse_moves(b, sq, piece):
            pb = dict(b)
            pb[a] = piece
            if not is_candidate(SETUP, pb, "file", True):
                continue
            mv = usi(a, sq)
            eng.position(to_sfen(pb, "b" if mover == "B" else "w"))
            if mv not in eng.legal() or eng.status() != "playing":
                continue
            yield pb, mv


def _digest(board):
    return hashlib.blake2b(repr(sorted(board.items())).encode(), digest_size=16).digest()


def relax(target, eng=None, depth=10, beam=12, tries=4, planner_retries=2, turn="B", log=None,
          compact_seen=False, fix_turn=False):
    """Returns (moves, info) with a certified game to `target` with `turn` to
    move, or (None, info).  compact_seen keeps a 16-byte digest of each visited board
    instead of the board (same search barring a digest collision; ~100x less memory).
    fix_turn=False keeps the behaviour of every run so far: the loop variable `turn` below
    shadows the argument, so certify() is asked for the previous level's side to move and
    only odd retraction depths can be certified (found 2026-10-20 by the C++ port; it only
    rejects valid games).  fix_turn=True certifies against the argument."""
    target_turn = turn
    key_of = _digest if compact_seen else (lambda b: frozenset(b.items()))
    eng = eng or Engine()
    info = {"tried": 0, "levels": 0}
    base = pocket_score(target)
    frontier = [(base, target, turn, [])]       # (score, board, side to move, forward moves to target)
    seen = {key_of(target)}
    for level in range(1, depth + 1):
        cands = []
        for _, board, turn, fwd in frontier:
            for pb, mv in predecessors(board, turn, eng):
                key = key_of(pb)
                if key in seen:
                    continue
                seen.add(key)
                pturn = "W" if turn == "B" else "B"
                cands.append((pocket_score(pb), pb, pturn, [mv] + fwd))
        if not cands:
            break
        cands.sort(key=lambda c: c[0])
        frontier = cands[:beam]
        info["levels"] = level
        for score, pb, pturn, fwd in frontier[:tries]:
            if score >= base:
                continue
            info["tried"] += 1
            for attempt in range(planner_retries):
                try:
                    pl = Planner(pb, eng, seed=attempt, end_turn=pturn)
                    moves = pl.run() + fwd
                except (PlannerError, Repetition):
                    continue
                except Exception:
                    continue
                ok, why = certify(moves, target, engine=eng, turn=target_turn if fix_turn else turn)
                if ok:
                    info.update({"ok": True, "retracted": len(fwd), "plies": len(moves), "score": (base, score)})
                    if log:
                        log(f"relax: rescued after {len(fwd)} retractions, score {base}->{score}")
                    return moves, info
    info["ok"] = False
    return None, info
