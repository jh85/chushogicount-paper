"""JCSA rules as a thin layer over the lishogi engine (docs/jcsa-delta.md).

Implemented: the counter-strike ban as sakishishi (R-L4 with H-3⑥: the ban
exists only if the lion to be taken back has a foot) extended to hit-and-run
captures on the mid square of a double move; the lance's missing last-rank
promotion (R-P4).  Bare king, stalemate and checkmate rows are bounded, not
implemented (docs/jcsa-delta.md).
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from count.sampler import to_sfen                                   # noqa: E402
from plan.moves import cheb, usi_sq, usi_squares                    # noqa: E402

LIONS = {"N", "+O"}            # lion, promoted kirin (merged role n / +o in SFEN)


def is_lion(piece):
    return piece is not None and piece[1] in LIONS


def _protected(engine, board, lion_sq, capturer_sq):
    """Could the lion's side move onto lion_sq if it held an enemy piece?  The
    capturer is lifted from its origin (X-rays through it count); no flag."""
    side = board[lion_sq][0]
    b = dict(board)
    del b[capturer_sq]
    b[lion_sq] = ("W" if side == "B" else "B", "P")     # dummy enemy piece to capture
    engine.position(to_sfen(b, "b" if side == "B" else "w"))
    tgt = usi_sq(lion_sq)
    for mv in engine.legal():
        sqs = usi_squares(mv)
        if sqs and sqs[-1] == lion_sq or (len(sqs) == 3 and sqs[1] == lion_sq):
            return True
    return False


def _lance_last_rank_promotion(board, mv, turn):
    """lishogi lets an unpromoted lance promote on reaching the last rank; JCSA
    (R-P4) does not: a lance promotes only on entering the zone (R-P1) or by
    capture (R-P2).  True for a lance promotion move that does neither."""
    if not mv.endswith("+"):
        return False
    sqs = usi_squares(mv)
    a, b = sqs[0], sqs[-1]
    if board.get(a) != (turn, "L"):
        return False
    entering = (a[1] < 9 if turn == "B" else a[1] > 4)      # origin outside the zone
    captures = b in board
    return not entering and not captures


def legal_moves(engine, board, turn, flag):
    """USI moves legal under JCSA: the engine's moves with the flag cleared,
    minus the lance's last-rank promotion (R-P4), minus the sakishishi ban
    (R-L4, H-3⑥).  `flag` is the counter-strike square ℓ or None."""
    engine.position(to_sfen(board, "b" if turn == "B" else "w"))      # flag cleared
    moves = {m for m in engine.legal() if not _lance_last_rank_promotion(board, m, turn)}
    if flag is None:
        return moves
    enemy = "W" if turn == "B" else "B"
    out = set()
    for mv in moves:
        sqs = usi_squares(mv)
        a, dest = sqs[0], sqs[-1]
        captured = [s for s in sqs[1:] if board.get(s, (None,))[0] == enemy]
        # Every enemy lion counts, including a promoted kirin standing on the capture square
        # (R-L4's kirin sentence): lishogi exempts the capture square, JCSA does not.
        lions_hit = [s for s in captured if is_lion(board[s])]
        if not lions_hit:
            out.add(mv)
            continue
        if is_lion(board.get(a)):
            # U1 (D11): the ban binds lions too, except an adjacent lion capture (R-L1) and a
            # capture through tsukegui (R-L5): an enemy piece taken on the mid square first
            exempt = all(cheb(a, s) == 1 for s in lions_hit) or \
                (len(sqs) == 3 and board.get(sqs[1], (None,))[0] == enemy and not is_lion(board[sqs[1]])
                 and lions_hit == [sqs[2]]) or \
                (len(sqs) == 3 and is_lion(board.get(sqs[1])) and cheb(a, sqs[1]) == 1)
            if exempt:
                out.add(mv)
                continue
        if all(not _protected(engine, board, s, a) for s in lions_hit):   # Okazaki rule (H-3⑥)
            out.add(mv)
    return out


def banned_by_jcsa(engine, board, turn, flag):
    """Engine-legal moves (flag cleared) that JCSA's ban removes."""
    engine.position(to_sfen(board, "b" if turn == "B" else "w"))
    return engine.legal() - legal_moves(engine, board, turn, flag)


def royal_capturable(jeng, board, side):
    """Can `side`'s opponent capture one of side's royals right now?"""
    other = "W" if side == "B" else "B"
    jeng.position(to_sfen(board, "b" if other == "B" else "w"))
    royals = {sq for sq, p in board.items() if p == (side, "K")}
    return any(any(s in royals for s in usi_squares(mv)[1:]) for mv in jeng.legal())


def other_side(turn):
    return "W" if turn == "B" else "B"


def mated(jeng, board, turn, flag, prince_escape=False, capture_escape=False):
    """JCSA R-E1 reading (docs/jcsa-rules-en.md U10): the side to move has exactly one
    royal, it is attacked, and every legal move leaves a royal capturable.  prince_escape
    (decision D13a): a move is an escape iff afterwards the opponent cannot capture all of the
    side's royals in one move; after a promotion to a prince (two royals, both written "K" on
    planner boards) that needs a double move capturing both.  capture_escape (decision D13b): a
    move that captures the opponent's last royal(s) is an escape (it ends the game)."""
    from count.sfen import parse
    if sum(1 for p in board.values() if p == (turn, "K")) != 1:
        return False
    if not royal_capturable(jeng, board, turn):
        return False
    opp_royal = any(p == (other_side(turn), "K") for p in board.values())
    sfen = to_sfen(board, "b" if turn == "B" else "w", usi_sq(flag) if flag else "-")
    jeng.position(sfen)
    for mv in list(jeng.legal()):
        jeng.position(sfen, [mv])
        after = parse(jeng.sfen())[0]
        if capture_escape and opp_royal and not any(p == (other_side(turn), "K") for p in after.values()):
            return False
        royals = {sq for sq, p in after.items() if p == (turn, "K")}
        if prince_escape and len(royals) >= 2:
            other = "W" if turn == "B" else "B"
            jeng.position(to_sfen(after, other.lower()))
            if not any(royals <= set(usi_squares(m)[1:]) for m in jeng.legal()):
                return False
            continue
        if not royal_capturable(jeng, after, turn):
            return False
    return True


def replay_jcsa(moves, eng, jeng, count_mates=False, prince_escape=False, capture_escape=False):
    """Replay a lishogi-legal game from the initial position; (ok, failing ply, move,
    category, mate plies).  ok iff every move is JCSA-legal (rows 1, 2, 4 of the delta
    table).  With count_mates, also list the plies at which the side to move is mated
    in the JCSA sense (U10), the final position excepted."""
    from count.sfen import INITIAL, parse
    eng.position(INITIAL)
    mates, fail = [], None
    for i, mv in enumerate(moves):
        board, turn, flag = parse(eng.sfen())
        if fail is None and (mv.endswith("+") or flag is not None):
            if mv not in legal_moves(jeng, board, turn, flag):
                cat = ("lance last-rank promotion (R-P4)" if _lance_last_rank_promotion(board, mv, turn)
                       else "capture of a protected lion during sakishishi (R-L4)")
                fail = (i, mv, cat)
        if count_mates and i < len(moves) - 1 and mated(jeng, board, turn, flag, prince_escape, capture_escape):
            mates.append(i)
        eng.move(mv)
    if fail:
        return (False,) + fail + (mates,)
    return True, None, None, None, mates
