"""Rules engine for small chu-like variants (validation, docs/validation-variant.md).

lishogi's chu shogi rules restricted to the pieces present: no check rule,
royals captured, optional promotion (entering the zone, capturing in or out of
it, pawn/lance on the last rank), lion double moves with igui and jitto,
lion-trading rules L1-L3 with the counter-strike flag, and every lishogi ending
(royals lost, bare king, stalemate, insufficient material).  Semantics follow
chushogi/src/movegen.cpp, position.cpp and status.cpp line by line.

A state is (board, turn, flag): board a tuple of length nfiles*nranks of piece
codes (0 empty, else index into PIECES + 1), turn 'B'/'W', flag a square index
or None.  Squares are indexed x * nranks + (r - 1), ranks from Black's side.

Roles: K N P L GB RC B G and promoted +P +L +GB +RC +B +G (same move tables as
plan/moves.py; the lion's double moves and lion-power rules are implemented here).
"""
from functools import lru_cache
from itertools import product

from plan.moves import MOVES, PROMOTES

ROYAL = ("K",)
LION = ("N",)
CONFINED = ("P", "L", "RC", "GB")


class Variant:
    def __init__(self, nfiles, nranks, zone, start, roles):
        """start: {(x, r): (colour, role)}; roles: all roles that can appear."""
        self.nf, self.nr, self.zone = nfiles, nranks, zone
        self.pieces = [(c, r) for c in "BW" for r in roles]
        self.code = {p: i + 1 for i, p in enumerate(self.pieces)}
        self.n = nfiles * nranks
        self.start_board = tuple(self.code[start[self.sq(i)]] if self.sq(i) in start else 0
                                 for i in range(self.n))
        self.start = (self.start_board, "B", None)

    # --- geometry ---------------------------------------------------------
    def sq(self, i):
        return i // self.nr, i % self.nr + 1

    def idx(self, x, r):
        return x * self.nr + r - 1

    def on(self, x, r):
        return 0 <= x < self.nf and 1 <= r <= self.nr

    def in_zone(self, colour, r):
        return r > self.nr - self.zone if colour == "B" else r <= self.zone

    def last_rank(self, colour):
        return self.nr if colour == "B" else 1

    def dist(self, i, j):
        a, b = self.sq(i), self.sq(j)
        return max(abs(a[0] - b[0]), abs(a[1] - b[1]))

    def piece(self, board, i):
        return self.pieces[board[i] - 1] if board[i] else None

    # --- attacks ------------------------------------------------------------
    def attacks(self, board, i, j, rem=()):
        """Can the piece on i capture on j (ignoring the mover's safety)?  Squares
        in rem are treated as empty."""
        colour, role = self.piece(board, i)
        sign = 1 if colour == "B" else -1
        (x, r), (tx, tr) = self.sq(i), self.sq(j)
        dx, dy = tx - x, (tr - r) * sign
        steps, slides = MOVES[role]
        if (dx, dy) in steps:
            return True
        for ux, uy in slides:
            if dx * uy != dy * ux or dx * ux + dy * uy <= 0:
                continue
            cx, cr = x + ux, r + uy * sign
            while (cx, cr) != (tx, tr):
                k = self.idx(cx, cr)
                if board[k] and k not in rem:
                    break
                cx, cr = cx + ux, cr + uy * sign
            else:
                return True
        return False

    def threatened(self, board, by, j, pawns_only=False, rem=()):
        for i in range(self.n):
            if i in rem or not board[i]:
                continue
            c, role = self.piece(board, i)
            if c != by or (pawns_only and role not in ("P", "GB")):
                continue
            if self.attacks(board, i, j, rem):
                return True
        return False

    def in_check(self, board, colour):
        other = "W" if colour == "B" else "B"
        return any(board[i] and self.piece(board, i) == (colour, "K") and self.threatened(board, other, i)
                   for i in range(self.n))

    # --- move generation ----------------------------------------------------
    def can_promote(self, role, colour, i, j, capture):
        if role not in PROMOTES:
            return False
        ri, rj = self.sq(i)[1], self.sq(j)[1]
        if self.in_zone(colour, rj) and not self.in_zone(colour, ri):
            return True
        if capture and (self.in_zone(colour, rj) or self.in_zone(colour, ri)):
            return True
        return role in ("P", "L") and rj == self.last_rank(colour)

    def legal_moves(self, state):
        """Moves as (i, mid, j, promote); mid is None for single moves."""
        board, us, flag = state
        them = "W" if us == "B" else "B"
        out = []
        for i in range(self.n):
            if not board[i] or self.piece(board, i)[0] != us:
                continue
            colour, role = self.piece(board, i)
            sign = 1 if us == "B" else -1
            x, r = self.sq(i)
            steps, slides = MOVES[role]
            short, dests = [], []
            for dx, dy in steps:
                tx, tr = x + dx, r + dy * sign
                if self.on(tx, tr):
                    j = self.idx(tx, tr)
                    if not board[j] or self.piece(board, j)[0] != us:
                        short.append(j)
            for ux, uy in slides:
                tx, tr = x + ux, r + uy * sign
                while self.on(tx, tr):
                    j = self.idx(tx, tr)
                    if board[j]:
                        if self.piece(board, j)[0] != us:
                            dests.append(j)
                        break
                    dests.append(j)
                    tx, tr = tx + ux, tr + uy * sign
            lion = role in LION
            for j in short + dests:
                occ = self.piece(board, j)
                if lion:
                    if occ and occ[1] in LION and self.dist(i, j) > 1 and \
                            self.threatened(board, them, j, False, (i,)):
                        continue
                elif flag is not None and j != flag and occ and occ[1] in LION:
                    continue
                out.append((i, None, j, False))
                if self.can_promote(role, us, i, j, occ is not None):
                    out.append((i, None, j, True))
            if not lion:
                continue
            for m in short:
                if self.dist(i, m) != 1:
                    continue
                out.append((i, m, i, False))                  # igui or jitto
                for j in short:
                    if self.dist(j, m) != 1:
                        continue
                    occ = self.piece(board, j)
                    if not occ or self.dist(j, i) == 1 or occ[1] not in LION:
                        out.append((i, m, j, False))
                        continue
                    mid = self.piece(board, m)
                    substantial = mid is not None and mid[1] not in ("P", "GB")
                    if substantial or (not self.threatened(board, them, j, False, (i, m)) and
                                       not self.threatened(board, them, j, True, (i,))):
                        out.append((i, m, j, False))
        return out

    def apply(self, state, move):
        board, us, flag = state
        i, m, j, promote = move
        b = list(board)
        mover = self.piece(board, i)
        old_j = self.piece(board, j) if j != i else None
        old_m = self.piece(board, m) if m is not None else None
        placed = (us, PROMOTES[mover[1]]) if promote else mover
        b[i] = 0
        b[j] = self.code[placed]
        if m is not None:
            b[m] = 0
        new_flag = None
        if mover[1] not in LION:
            if old_j and old_j[1] in LION:
                new_flag = j
            elif old_m and old_m[1] in LION:
                new_flag = m
        return tuple(b), ("W" if us == "B" else "B"), new_flag

    # --- game end (lishogi status, same order) ----------------------------------
    def dead(self, colour, role, i):
        return role in ("P", "L") and self.sq(i)[1] == self.last_rank(colour)

    def bare_king(self, board, colour):
        ours = royals = theirs = their_royals = 0
        royal_sq = None
        for i in range(self.n):
            if board[i] and self.piece(board, i) == (colour, "K"):
                royal_sq = i
        adjacent = False
        for i in range(self.n):
            if not board[i]:
                continue
            c, role = self.piece(board, i)
            if c == colour:
                if not self.dead(c, role, i):
                    ours += 1
                if role in ROYAL:
                    royals += 1
            else:
                if role not in ("P", "GB") and not self.dead(c, role, i):
                    theirs += 1
                    if royal_sq is not None and self.dist(royal_sq, i) == 1:
                        adjacent = True
                if role in ROYAL:
                    their_royals += 1
        # (status.cpp detects adjacency only for enemy pieces scanned after the
        # royal; that depends on square order and is treated as an artifact here)
        other = "W" if colour == "B" else "B"
        return (ours == 1 and royals == 1 and theirs > 1 and their_royals >= 1 and
                not self.in_check(board, other) and (theirs > 2 or not adjacent))

    def status(self, state):
        board, us, flag = state
        if not any(board[i] and self.piece(board, i) == (us, "K") for i in range(self.n)):
            return "royalslost"
        if self.bare_king(board, "B") or self.bare_king(board, "W"):
            return "bareking"
        if not self.legal_moves(state):
            return "stalemate"
        live = sum(1 for i in range(self.n) if board[i] and not self.dead(*self.piece(board, i), i))
        rb = sum(1 for i in range(self.n) if board[i] and self.piece(board, i) == ("B", "K"))
        rw = sum(1 for i in range(self.n) if board[i] and self.piece(board, i) == ("W", "K"))
        if live == 2 and rb == 1 and rw == 1 and not self.in_check(board, "B") and not self.in_check(board, "W"):
            return "draw"
        return "playing"

    def to_board_dict(self, board):
        return {self.sq(i): self.piece(board, i) for i in range(self.n) if board[i]}
