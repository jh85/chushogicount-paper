"""lishogi chu shogi SFEN -> board dict used by candidates.is_candidate.

Board: {(x, r): (colour, role)}, x = 0..11 from Black's left (file a = lishogi
file 12), r = 1..12 from Black's side (lishogi rank l = 1).  Promoted kirin,
phoenix and drunk elephant are written as lion 'N', free king 'Q' and king 'K'
(decision D2); every other promoted piece is '+' + base role.
"""
BASE = {"p": "P", "l": "L", "i": "GB", "a": "RC", "m": "M", "v": "V", "c": "C", "s": "S",
        "f": "F", "t": "T", "g": "G", "e": "E", "b": "B", "r": "R", "h": "H", "d": "D",
        "o": "O", "x": "X", "k": "K", "n": "N", "q": "Q"}
IDENTIFIED = {"+O": "N", "+X": "Q", "+E": "K"}
INITIAL = ("lfcsgekgscfl/a1b1txot1b1a/mvrhdqndhrvm/pppppppppppp/3i4i3/12/12/"
           "3I4I3/PPPPPPPPPPPP/MVRHDNQDHRVM/A1B1TOXT1B1A/LFCSGKEGSCFL b - 1")


def _parse_reference(sfen):
    """Returns (board, side to move 'B'/'W', lion flag as (x, r) or None)."""
    rows, turn, flag = sfen.split()[:3]
    board = {}
    for i, row in enumerate(rows.split("/")):
        r, x, num, promoted = 12 - i, 0, "", False
        for ch in row + " ":
            if ch.isdigit():
                num += ch
                continue
            if num:
                x += int(num)
                num = ""
            if ch == "+":
                promoted = True
            elif ch != " ":
                role = ("+" if promoted else "") + BASE[ch.lower()]
                board[(x, r)] = ("B" if ch.isupper() else "W", IDENTIFIED.get(role, role))
                x, promoted = x + 1, False
        assert x == 12, sfen
    sq = None if flag == "-" else (12 - int(flag[:-1]), 12 - "abcdefghijkl".index(flag[-1]))
    return board, "B" if turn == "b" else "W", sq


_PIECE = {}
for _ch, _role in BASE.items():
    for _p in (False, True):
        _r = ("+" if _p else "") + _role
        _PIECE[_p, _ch] = ("W", IDENTIFIED.get(_r, _r))
        _PIECE[_p, _ch.upper()] = ("B", IDENTIFIED.get(_r, _r))


def parse(sfen):
    """Returns (board, side to move 'B'/'W', lion flag as (x, r) or None).  Same result
    as _parse_reference (the original loop), table-driven for the planner's hot path."""
    rows, turn, flag = sfen.split()[:3]
    board = {}
    r = 12
    for row in rows.split("/"):
        x, num, promoted = 0, 0, False
        for ch in row:
            if "0" <= ch <= "9":
                num = num * 10 + ord(ch) - 48
            elif ch == "+":
                x, num, promoted = x + num, 0, True
            else:
                x += num
                board[(x, r)] = _PIECE[promoted, ch]
                x, num, promoted = x + 1, 0, False
        x += num
        assert x == 12, sfen
        r -= 1
    sq = None if flag == "-" else (12 - int(flag[:-1]), 12 - "abcdefghijkl".index(flag[-1]))
    return board, "B" if turn == "b" else "W", sq
