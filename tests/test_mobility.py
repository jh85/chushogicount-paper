#!/usr/bin/env python3
"""Which pieces are restricted to part of the board when nothing is in the way?

On an empty board, from every square, compute the set of squares a single piece
can reach (Black's orientation; White is the 180-degree rotation).  Expected
(docs/invariants.md, I1, I6, I7):
  * pawn, lance, reverse chariot, go-between: their own file only (pawn and
    lance: only forwards);
  * bishop, kirin (and the leopard's promoted form, which moves as a bishop):
    one colour class, all 72 squares of it;
  * every other role: all 144 squares, from every square (strongly connected).
Move tables transcribed from docs/spec.md section 2 (lion-power double moves add
no new destinations and are omitted).
"""
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
                       "+B": "H", "+R": "D", "+E": "K"}.items():
    MOVES[promoted] = MOVES[base]
SQUARES = [(x, r) for x in range(12) for r in range(1, 13)]


def reach(role, start):
    steps, slides = MOVES[role]
    seen, stack = {start}, [start]
    while stack:
        x, r = stack.pop()
        for dx, dy in steps + [(k * dx, k * dy) for dx, dy in slides for k in range(1, 12)]:
            t = (x + dx, r + dy)
            if 0 <= t[0] < 12 and 1 <= t[1] <= 12 and t not in seen:
                seen.add(t)
                stack.append(t)
    return seen


def test_mobility():
    assert len(MOVES) == 21 + 18 - 2          # +O and +X are N and Q
    for role in MOVES:
        for s in SQUARES:
            got = reach(role, s)
            if role in ("P", "L"):
                want = {(s[0], r) for r in range(s[1], 13)}
            elif role in ("GB", "RC"):
                want = {(s[0], r) for r in range(1, 13)}
            elif role in ("B", "O", "+F"):
                want = {t for t in SQUARES if (t[0] + t[1]) % 2 == (s[0] + s[1]) % 2}
            else:
                want = set(SQUARES)
            assert got == want, (role, s, len(got))


if __name__ == "__main__":
    test_mobility()
    print("ok test_mobility")
