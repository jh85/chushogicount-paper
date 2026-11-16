"""Piece geometry for planning: move tables, square helpers, path search.

Roles as in count/sfen.py (merged: N, Q, K).  Directions are Black's; White's
are mirrored in rank.  The engine remains the authority on legality.
"""
from collections import deque

N, S, E, W, NE, NW, SE, SW = (0, 1), (0, -1), (1, 0), (-1, 0), (1, 1), (-1, 1), (1, -1), (-1, -1)
ORTH, DIAG = [N, S, E, W], [NE, NW, SE, SW]
ALL = ORTH + DIAG
J = lambda d: (2 * d[0], 2 * d[1])
MOVES = {  # role: (steps/jumps, slides)
    "P": ([N], []), "GB": ([N, S], []), "L": ([], [N]), "RC": ([], [N, S]),
    "M": ([N, S], [E, W]), "V": ([E, W], [N, S]), "C": ([N, NE, NW, S], []),
    "S": ([N, NE, NW, SE, SW], []), "F": ([N, S] + DIAG, []),
    "T": ([d for d in ALL if d != N], []), "G": ([N, S, E, W, NE, NW], []),
    "E": ([d for d in ALL if d != S], []), "B": ([], DIAG), "R": ([], ORTH),
    "H": (ORTH, DIAG), "D": (DIAG, ORTH), "O": (DIAG + [J(d) for d in ORTH], []),
    "X": (ORTH + [J(d) for d in DIAG], []), "K": (ALL, []),
    "N": ([(dx, dy) for dx in range(-2, 3) for dy in range(-2, 3) if (dx, dy) != (0, 0)], []),
    "Q": ([], ALL),
    "+L": ([], [N, S, NE, NW]), "+RC": ([], [N, S, SE, SW]), "+M": ([], [E, W] + DIAG),
    "+V": ([], [N, S] + DIAG), "+T": ([E, W] + DIAG, [N, S]),
    "+H": ([N, J(N)], [d for d in ALL if d != N]), "+D": ([NE, NW, J(NE), J(NW)], [N, S, E, W, SE, SW]),
}
for promoted, base in {"+P": "G", "+GB": "E", "+C": "M", "+S": "V", "+F": "B", "+G": "R",
                       "+B": "H", "+R": "D"}.items():
    MOVES[promoted] = MOVES[base]
PROMOTES = {"P": "+P", "GB": "+GB", "L": "+L", "RC": "+RC", "M": "+M", "V": "+V", "C": "+C",
            "S": "+S", "F": "+F", "T": "+T", "G": "+G", "E": "K", "B": "+B", "R": "+R",
            "H": "+H", "D": "+D", "O": "N", "X": "Q"}
CONFINED = ("P", "L", "RC", "GB")
SQUARES = [(x, r) for x in range(12) for r in range(1, 13)]
RANKS = "abcdefghijkl"


def on_board(sq):
    return 0 <= sq[0] < 12 and 1 <= sq[1] <= 12


def usi_sq(sq):
    return f"{12 - sq[0]}{RANKS[12 - sq[1]]}"


def from_usi_sq(s):
    return 12 - int(s[:-1]), 12 - RANKS.index(s[-1])


def usi_squares(mv):
    """All squares named in a USI move string, in order."""
    import re
    return [from_usi_sq(f + r) for f, r in re.findall(r"(\d+)([a-l])", mv)]


def usi(frm, to, promote=False, mid=None):
    return usi_sq(frm) + (usi_sq(mid) if mid else "") + usi_sq(to) + ("+" if promote else "")


def in_zone(colour, sq):
    return sq[1] >= 9 if colour == "B" else sq[1] <= 4


def cheb(a, b):
    return max(abs(a[0] - b[0]), abs(a[1] - b[1]))


def single_moves(board, sq, piece=None):
    """Destinations of single moves (no captures of own pieces; captures of enemy
    pieces allowed) for the piece on sq, ignoring lion-trading rules."""
    colour, role = piece or board[sq]
    sign = 1 if colour == "B" else -1
    steps, slides = MOVES[role]
    out = []
    for dx, dy in steps:
        t = (sq[0] + dx, sq[1] + dy * sign)
        if on_board(t) and (t not in board or board[t][0] != colour):
            out.append(t)
    for dx, dy in slides:
        t = (sq[0] + dx, sq[1] + dy * sign)
        while on_board(t):
            if t in board:
                if board[t][0] != colour:
                    out.append(t)
                break
            out.append(t)
            t = (t[0] + dx, t[1] + dy * sign)
    return out


def adjacent_dests(sq, piece):
    """First square in every direction of the piece's move set (occupied or not)."""
    colour, role = piece
    sign = 1 if colour == "B" else -1
    steps, slides = MOVES[role]
    out = []
    for dx, dy in steps + slides:
        t = (sq[0] + dx, sq[1] + dy * sign)
        if on_board(t):
            out.append(t)
    return out


def path(board, sq, goals, walls=frozenset(), piece=None, capture=False, max_len=40):
    """Shortest sequence of destination squares for the piece on sq to reach any
    square in `goals` through empty squares (or, with capture=True, ending with a
    capture on the goal).  `walls` are squares that must not be entered."""
    colour, role = piece or board[sq]
    goals = set(goals)
    prev = {sq: None}
    q = deque([sq])
    while q:
        cur = q.popleft()
        if cur in goals and cur != sq:
            out = []
            while cur != sq:
                out.append(cur)
                cur = prev[cur]
            return out[::-1]
        if len(prev) > 2000:
            break
        b = dict(board)
        del b[sq]
        b[cur] = (colour, role)
        for t in single_moves(b, cur):
            if t in prev or t in walls:
                continue
            if t in b:                       # occupied: only as a capturing goal
                if capture and t in goals and b[t][0] != colour:
                    prev[t] = cur
                    q.append(t)
                continue
            prev[t] = cur
            q.append(t)
    return None


def traversed(piece, a, b):
    """Squares strictly between a and b that a sliding move from a to b crosses
    (empty for steps and jumps)."""
    colour, role = piece
    sign = 1 if colour == "B" else -1
    dx, dy = b[0] - a[0], (b[1] - a[1]) * sign
    steps, slides = MOVES[role]
    if (dx, dy) in steps:
        return []
    n = max(abs(dx), abs(dy))
    if n <= 1:
        return []
    ux, uy = dx // n, dy // n
    return [(a[0] + ux * i, a[1] + uy * sign * i) for i in range(1, n)]


def ascii_board(board):
    rows = []
    for r in range(12, 0, -1):
        cells = []
        for x in range(12):
            p = board.get((x, r))
            if p is None:
                cells.append(" . ")
            else:
                role = p[1]
                cells.append((role if p[0] == "B" else role.lower()).rjust(3))
        rows.append(f"{r:2d} " + "".join(cells))
    return "\n".join(rows) + "\n    " + "".join(f"  {c}" for c in "abcdefghijkl")


def reverse_moves(board, sq, piece):
    """Empty squares from which `piece` could have moved to sq (sliders need the
    path clear; steps and jumps are reversed vectors)."""
    colour, role = piece
    sign = 1 if colour == "B" else -1
    steps, slides = MOVES[role]
    out = []
    for dx, dy in steps:
        t = (sq[0] - dx, sq[1] - dy * sign)
        if on_board(t) and t not in board:
            out.append(t)
    for dx, dy in slides:
        t = (sq[0] - dx, sq[1] - dy * sign)
        while on_board(t) and t not in board:
            out.append(t)
            t = (t[0] - dx, t[1] - dy * sign)
    return out
