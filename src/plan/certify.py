"""Certificate checker: a proof game is accepted only if the reference engine
replays every move as legal, no position is terminal before the last ply, no
state (board, side to move, flag) repeats, and the final state equals the
target exactly: board, Black to move, and the counter-strike flag (None, or the
square of a flag-on certificate).  Independent of the planner."""
import sys
from pathlib import Path

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from count.sfen import INITIAL, parse            # noqa: E402
from plan.engine import Engine                  # noqa: E402


def certify(moves, target, flag=None, engine=None, target_status=None, turn="B"):
    """Returns (ok, reason).  target_status: the engine status the target must
    have ('playing' for a non-terminal target); computed if not given."""
    eng = engine or Engine()
    if target_status is None:
        from count.sampler import to_sfen
        eng.position(to_sfen(target, "b" if turn == "B" else "w"))
        target_status = eng.status()
    eng.position(INITIAL)
    seen = set()
    for i, mv in enumerate(moves):
        board, side, fl = parse(eng.sfen())
        key = (frozenset(board.items()), side, fl)
        if key in seen:
            return False, f"repetition before ply {i}"
        seen.add(key)
        if mv not in eng.legal():
            return False, f"illegal move {mv} at ply {i}"
        if i > 0 and eng.status() != "playing":
            return False, f"terminal position before ply {i}"
        eng.move(mv)
    board, final_turn, fl = parse(eng.sfen())
    if final_turn != turn:
        return False, f"{final_turn} to move at the end, expected {turn}"
    if fl != flag:
        return False, f"final flag {fl}, expected {flag}"
    if board != target:
        return False, "final board differs from the target"
    if eng.status() != target_status:
        return False, f"final status {eng.status()}, target has {target_status}"
    return True, f"{len(moves)} plies"
