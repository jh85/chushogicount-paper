"""JCSA layer, smoke tests (JCSA worked examples pending: docs/jcsa-delta.md)."""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "src"))
from count.sampler import to_sfen                     # noqa: E402
from plan.engine import Engine                        # noqa: E402
from plan.moves import usi, usi_sq                    # noqa: E402
from jcsa.mode import legal_moves, banned_by_jcsa     # noqa: E402

eng = Engine()
K, k = ("B", "K"), ("W", "K")


def lishogi_legal(board, turn, flag):
    eng.position(to_sfen(board, "b" if turn == "B" else "w", usi_sq(flag) if flag else "-"))
    return eng.legal()


def test_no_flag_identical():
    board = {(0, 1): K, (11, 12): k, (5, 5): ("B", "R"), (5, 9): ("W", "N")}
    assert legal_moves(eng, board, "B", None) == lishogi_legal(board, "B", None)
    print("ok no flag: identical to the engine")


def test_okazaki_unprotected_lion_capturable():
    # Black rook f5 attacks the White lion f9 (unprotected); ban active on another square
    board = {(0, 1): K, (11, 12): k, (5, 5): ("B", "R"), (5, 9): ("W", "N")}
    flag = (2, 3)
    cap = usi((5, 5), (5, 9))
    assert cap not in lishogi_legal(board, "B", flag), "lishogi bans the capture"
    assert cap in legal_moves(eng, board, "B", flag), "JCSA allows capturing an unprotected lion"
    print("ok Okazaki: unprotected lion capturable under JCSA, banned under lishogi")


def test_protected_lion_banned():
    # same, with a White gold on g10 protecting f9
    board = {(0, 1): K, (11, 12): k, (5, 5): ("B", "R"), (5, 9): ("W", "N"), (6, 10): ("W", "G")}
    flag = (2, 3)
    cap = usi((5, 5), (5, 9))
    assert cap in legal_moves(eng, board, "B", None)
    assert cap not in legal_moves(eng, board, "B", flag), "JCSA bans capturing a protected lion"
    assert cap in banned_by_jcsa(eng, board, "B", flag)
    print("ok protected lion: banned under JCSA")


def test_capture_on_flag_square():
    # a lion standing on the flag square is a kirin that captured there and promoted: under
    # JCSA it is covered by the ban when it has a foot (lishogi exempts the capture square)
    board = {(0, 1): K, (11, 12): k, (5, 5): ("B", "R"), (5, 9): ("W", "N"), (6, 10): ("W", "G")}
    cap = usi((5, 5), (5, 9))
    assert cap in lishogi_legal(board, "B", (5, 9)), "lishogi exempts the capture square"
    assert cap not in legal_moves(eng, board, "B", (5, 9)), "JCSA: protected promoted kirin on the capture square is banned"
    del board[(6, 10)]
    assert cap in legal_moves(eng, board, "B", (5, 9)), "JCSA: unprotected promoted kirin may be taken"
    board2 = {(0, 1): K, (11, 12): k, (5, 5): ("B", "R"), (5, 9): ("W", "G"), (6, 10): ("W", "G")}
    assert cap in legal_moves(eng, board2, "B", (5, 9)), "a non-lion capturer on the capture square may always be taken"
    print("ok capture square: non-lion capturer takable; promoted kirin banned iff protected")


def test_cases_json():
    """Every recorded case keeps its engine verdict (lishogi) and, where the layer
    implements the rule, its JCSA verdict."""
    import json
    from plan.moves import usi_squares
    from count.sfen import parse
    cases = json.load(open(Path(__file__).resolve().parents[1] / "out" / "fixtures" / "jcsa" / "cases.json"))
    for c in cases:
        board, turn, flag = parse(c["sfen"])
        if c["move"] == "(status)":
            eng.position(c["sfen"])
            assert eng.status() == c["verdict_lishogi"], c["id"]
            continue
        eng.position(c["sfen"])
        moves = eng.legal()
        if "(any route)" in c["move"]:
            a, b = c["move"].split(" ")[0].split("->")
            from plan.moves import from_usi_sq
            frm, to = from_usi_sq(a), from_usi_sq(b)
            hit = any(usi_squares(m)[0] == frm and usi_squares(m)[-1] == to for m in moves)
            assert ("legal" if hit else "illegal") == c["verdict_lishogi"], c["id"]
        else:
            assert ("legal" if c["move"] in moves else "illegal") == c["verdict_lishogi"], c["id"]
            if c["verdict_jcsa_layer"] in ("legal", "illegal"):
                jl = legal_moves(eng, board, turn, flag)
                assert ("legal" if c["move"] in jl else "illegal") == c["verdict_jcsa"], c["id"]
    print(f"ok {len(cases)} recorded cases re-verified")


if __name__ == "__main__":
    test_no_flag_identical()
    test_okazaki_unprotected_lion_capturable()
    test_protected_lion_banned()
    test_capture_on_flag_square()
    test_cases_json()
    print("ok")