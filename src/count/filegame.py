"""Abstract file game: exact per-file admissibility of confined pieces.

A "confined" piece (unpromoted pawn, lance, reverse chariot, go-between) never
leaves its starting file.  Project any real game onto one file f and forget
everything except the confined pieces that started on f ("slots").  Each slot is
in one of three states: unpromoted on the file at some rank, promoted (it has
left the abstraction), or captured.  The projection of a legal game is a play of
the following abstract game, so every state NOT reachable here is unreachable in
the real game (docs/invariants.md, Theorem F):

  * any unpromoted slot may disappear at any time (captured by anything);
  * an unpromoted slot may move along the file as its piece type allows, onto a
    square not occupied by another unpromoted slot of the file (capturing an
    enemy slot = "disappear, then move"), never passing over one;
  * a move may promote iff its origin or its destination lies in the mover's
    promotion zone (entering always allows it; inside the zone a capture is
    needed, and the abstraction lets every move be a capture of a non-slot
    piece; the last-rank rule for pawn/lance is a special case).

Ranks are 1..R counted from Black's side; Black moves towards rank R.
"""
from collections import namedtuple
from functools import lru_cache

Slot = namedtuple("Slot", "name colour kind start")   # colour 'B'/'W'; kind P/L/RC/GB

CAPTURED, PROMOTED = 0, -1


def in_zone(colour, rank, R, Z):
    return rank > R - Z if colour == "B" else rank <= Z


def _dests(slot, r, occ, R):
    d = 1 if slot.colour == "B" else -1
    if slot.kind == "P":
        steps, slide = (d,), False
    elif slot.kind == "GB":
        steps, slide = (d, -d), False
    elif slot.kind == "L":
        steps, slide = (d,), True
    elif slot.kind == "RC":
        steps, slide = (d, -d), True
    else:
        raise ValueError(slot.kind)
    for s in steps:
        b = r + s
        while 1 <= b <= R and b not in occ:
            yield b
            if not slide:
                break
            b += s


def reachable_states(slots, R, Z):
    """All reachable states; a state is a tuple with, per slot, its rank (>0),
    CAPTURED or PROMOTED."""
    start = tuple(s.start for s in slots)
    seen = {start}
    stack = [start]
    while stack:
        st = stack.pop()
        occ = {r for r in st if r > 0}
        for i, r in enumerate(st):
            if r <= 0:
                continue
            nxt = [st[:i] + (CAPTURED,) + st[i + 1:]]
            for b in _dests(slots[i], r, occ, R):
                nxt.append(st[:i] + (b,) + st[i + 1:])
                if in_zone(slots[i].colour, r, R, Z) or in_zone(slots[i].colour, b, R, Z):
                    nxt.append(st[:i] + (PROMOTED,) + st[i + 1:])
            for t in nxt:
                if t not in seen:
                    seen.add(t)
                    stack.append(t)
    return seen


def admissible(slots, R, Z):
    """dict: U-config (tuple of rank or 0 per slot) -> set of frozensets of slot
    indices that can be 'promoted' while exactly the U-config stays unpromoted on
    the file and every other slot is captured."""
    out = {}
    for st in reachable_states(slots, R, Z):
        u = tuple(r if r > 0 else 0 for r in st)
        out.setdefault(u, set()).add(frozenset(i for i, r in enumerate(st) if r == PROMOTED))
    return out


# ---- chu shogi files -------------------------------------------------------
def chu_file_slots(x):
    """Slots of file index x (0 = file a = Black's left = lishogi file 12)."""
    if x in (0, 11):
        return [Slot("BL", "B", "L", 1), Slot("BRC", "B", "RC", 2), Slot("BP", "B", "P", 4),
                Slot("WP", "W", "P", 9), Slot("WRC", "W", "RC", 11), Slot("WL", "W", "L", 12)]
    if x in (3, 8):
        return [Slot("BP", "B", "P", 4), Slot("BGB", "B", "GB", 5),
                Slot("WGB", "W", "GB", 8), Slot("WP", "W", "P", 9)]
    return [Slot("BP", "B", "P", 4), Slot("WP", "W", "P", 9)]


def path_to(slots, R, Z, target, strict=True):
    """Shortest abstract play from the start to `target` (a state tuple), as a
    list of (slot index, from_rank, to_rank or CAPTURED/PROMOTED).  With
    strict=True promotion is only allowed on a non-capturing move that enters the
    zone or takes a pawn/lance to the last rank (what a planner can always do
    without a capture); the superset rule of reachable_states is used otherwise.
    Captures (-> CAPTURED) are listed first.  None if unreachable.
    The BFS tree is computed once per (slots, R, Z, strict) and cached: BFS assigns
    each state's parent at first discovery, so the path to `target` is the same as
    that of a search stopped at `target`."""
    prev = _bfs_tree(tuple(slots), R, Z, strict)
    if target not in prev:
        return None
    out, cur = [], target
    while prev[cur] is not None:
        cur, mv = prev[cur]
        out.append(mv)
    out.reverse()
    caps = [m for m in out if m[2] == CAPTURED]
    return caps + [m for m in out if m[2] != CAPTURED]


@lru_cache(maxsize=None)
def _bfs_tree(slots, R, Z, strict):
    from collections import deque
    start = tuple(s.start for s in slots)
    prev = {start: None}
    q = deque([start])
    while q:
        st = q.popleft()
        occ = {r for r in st if r > 0}
        for i, r in enumerate(st):
            if r <= 0:
                continue
            nxt = [(st[:i] + (CAPTURED,) + st[i + 1:], (i, r, CAPTURED))]
            for b in _dests(slots[i], r, occ, R):
                nxt.append((st[:i] + (b,) + st[i + 1:], (i, r, b)))
                if strict:
                    last = R if slots[i].colour == "B" else 1
                    ok = (in_zone(slots[i].colour, b, R, Z) and not in_zone(slots[i].colour, r, R, Z)) or \
                         (slots[i].kind in ("P", "L") and b == last)
                else:
                    ok = in_zone(slots[i].colour, r, R, Z) or in_zone(slots[i].colour, b, R, Z)
                if ok:
                    nxt.append((st[:i] + (PROMOTED,) + st[i + 1:], (i, r, b, PROMOTED)))
            for t, mv in nxt:
                if t not in prev:
                    prev[t] = (st, mv)
                    q.append(t)
    return prev
