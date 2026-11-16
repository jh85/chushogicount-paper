"""Effective counter-strike flag states under JCSA's ban (docs/jcsa-delta.md rows 1–2),
paired with the lishogi count on the same board.

A flag state (board, ℓ) is effective iff the ban removes at least one legal Black
move; two flags removing the same moves are one state (D3).  lishogi removes every
capture of a lion by a non-lion on a square ≠ ℓ (destination only).  JCSA removes
such a capture (destination or mid square) only if the captured lion is protected
(Okazaki rule).  The engine (flag cleared) lists the candidate captures; protection
is an engine query (`jcsa.mode._protected`).
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from count.sampler import to_sfen                            # noqa: E402
from jcsa.mode import _protected, is_lion                    # noqa: E402
from plan.flags import realizable_flags                      # noqa: E402
from plan.moves import usi_squares                           # noqa: E402


def lion_captures(engine, board):
    """Black non-lion moves capturing a White lion, flag cleared:
    [(usi, origin, lion square, on_mid)]."""
    engine.position(to_sfen(board, "b"))
    out = []
    for mv in engine.legal():
        sqs = usi_squares(mv)
        a = sqs[0]
        if is_lion(board.get(a)):
            continue
        for i, s in enumerate(sqs[1:]):
            p = board.get(s)
            if p is not None and p[0] == "W" and is_lion(p):
                out.append((mv, a, s, i < len(sqs) - 2))
    return out


def effective_states_both(engine, board):
    """(k_lishogi, k_jcsa) for a non-terminal board; (0, 0) if no realizable flag."""
    flags = realizable_flags(board)
    if not flags:
        return 0, 0
    caps = lion_captures(engine, board)
    if not caps:
        return 0, 0
    prot = {}
    for mv, a, s, on_mid in caps:
        if (s, a) not in prot:
            prot[(s, a)] = _protected(engine, board, s, a)
    seen_l, seen_j = set(), set()
    for l in flags:
        banned_l = frozenset(mv for mv, a, s, on_mid in caps if s != l and not on_mid)
        banned_j = frozenset(mv for mv, a, s, on_mid in caps if prot[(s, a)])      # capture square not exempt under JCSA
        if banned_l:
            seen_l.add(banned_l)
        if banned_j:
            seen_j.add(banned_j)
    return len(seen_l), len(seen_j)


def jcsa_states(engine, board):
    """Distinct JCSA flag states of a non-terminal board: [(ℓ, banned move set)], one
    representative ℓ per distinct non-empty banned set (D3 under JCSA's ban)."""
    flags = realizable_flags(board)
    if not flags:
        return []
    caps = lion_captures(engine, board)
    if not caps:
        return []
    prot = {}
    for mv, a, s, on_mid in caps:
        if (s, a) not in prot:
            prot[(s, a)] = _protected(engine, board, s, a)
    seen, out = set(), []
    for l in flags:
        banned = frozenset(mv for mv, a, s, on_mid in caps if prot[(s, a)])        # capture square not exempt under JCSA
        if banned and banned not in seen:
            seen.add(banned)
            out.append((l, banned))
    return out
