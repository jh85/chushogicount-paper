"""Proof-game planner prototype (decision D6).

Given a target board (Black to move, flag none), construct a legal game from the
initial position that ends in exactly that position.  Every move is taken from
the engine's legal-move list, so a finished game is a proof of reachability.

Phases (docs/lemma.md section 5, run forwards):
  0  both lions jump out of the camps (tempo by jitto from then on)
  A  captures: every piece absent from the target is taken by the enemy lion
  B  confined pieces follow a shortest play of the abstract file game (strict
     promotion rule), file by file
  C  free pieces that are promoted in the target walk into the zone
  D  all remaining pieces are routed to their target squares (BFS through empty
     squares; blocking pieces are displaced)
  E  lions that must die are captured on the capturer's target square; the
     terminal capture (Black's last royal) is the final move; parity is fixed
     with jitto or a king triangle
Waiting moves: jitto if the side has a lion, otherwise a reversible step that is
undone at the next opportunity.

Failures raise PlannerError(phase, reason); the caller classifies them.
"""
import random
import sys
from collections import Counter, defaultdict
from pathlib import Path

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from count import filegame                                         # noqa: E402
from count.filegame import CAPTURED, PROMOTED                      # noqa: E402
from count.sfen import INITIAL, parse                               # noqa: E402
from plan.engine import Engine                                     # noqa: E402
from count.candidates import sq_class                              # noqa: E402
from plan.moves import (CONFINED, PROMOTES, SQUARES, adjacent_dests, cheb, in_zone,  # noqa: E402
                        path, reverse_moves, single_moves, traversed, usi, usi_squares)

OTHER = {"B": "W", "W": "B"}
WALLS = ("P", "L")          # confined pieces that never move backwards: fixed obstacles
FLUID_CONFINED = ("RC", "GB")   # confined but reversible along their file
BASE = {"+P": "P", "+GB": "GB", "+L": "L", "+RC": "RC"}
# roles with a move set closed under reversal (usable for waiting pairs)
REVERSIBLE = {"K", "Q", "R", "B", "H", "D", "M", "V", "F", "N",
              "+B", "+R", "+M", "+V", "+S", "+C", "+F", "+T"}      # no confined pieces
MAX_PLIES = 6000


class Repetition(Exception):
    """A state repeated: the attempt is void (never swallowed like PlannerError)."""


class PlannerError(Exception):
    def __init__(self, phase, reason, at=None):
        super().__init__(f"{phase}: {reason}")
        self.phase, self.reason, self.at = phase, reason, at   # at: where the routed piece is now


class Planner:
    def __init__(self, target, engine=None, verbose=False, seed=0, flag=None, origin=None, end_turn="B",
                 strategy=None, defer=False, park=False):
        """flag: a square l for a flag-on certificate: the game must end with a
        White non-lion capturing a Black lion on l (the White piece of the
        target on l is the capturer; it must not need to promote on that move)."""
        self.target = dict(target)
        self.flag_target = flag
        self.forced_origin = origin         # origin square of the final capture, if prescribed
        self.end_turn = end_turn            # side to move in the final position
        # placement strategy: 'greedy' / 'peel' (baseline, by seed parity) / 'edge' (fallback)
        self.strategy = strategy or ("greedy" if seed % 2 == 0 else "peel")
        self.defer = defer                  # defer sealing pawn/lance moves (fallback option)
        self.park = park                    # displace() avoids squares the piece could not leave (fallback option)
        self.eng = engine or Engine()
        self.eng.position(INITIAL)
        self.moves = []
        self.seen = set()               # states visited, for repetition-free games
        self.pending = {"B": [], "W": []}       # return moves of waiting pairs
        self.verbose = verbose
        self.phase = "init"
        self.fluid_ok = False       # may reverse chariots / go-betweens be displaced?
        self.reserved = set()       # squares a route in progress needs; waiting moves avoid them
        self.protected = set()      # squares of pieces being worked on; waiting moves never use them
        self.rng = random.Random(seed)
        self.rng_seed = seed
        self.sync()
        self.seen.add(self.state())

    def state(self):
        return (frozenset(self.board.items()), self.turn, self.flag)

    def is_wall(self, role):
        return role in WALLS or (role in FLUID_CONFINED and not self.fluid_ok)

    # --- engine interface ---------------------------------------------------
    def sync(self):
        self.board, self.turn, self.flag = parse(self.eng.sfen())

    def would_repeat(self, mv):
        """Resulting state of a simple non-capturing single move, if it was seen."""
        sqs = usi_squares(mv)
        if len(sqs) != 2 or mv.endswith("+") or sqs[1] in self.board:
            return False
        nb = dict(self.board)
        nb[sqs[1]] = nb.pop(sqs[0])
        return (frozenset(nb.items()), OTHER[self.turn], None) in self.seen

    def play(self, side, mv, _retry=3):
        assert self.turn == side, (self.turn, side, mv)
        if _retry and self.would_repeat(mv):
            # perturb with a reversible step of another piece first (undone later)
            self.perturb(side, usi_squares(mv)[0])
            while self.turn != side:
                self.wait(self.turn)
            if usi_squares(mv)[1] in self.board:
                raise PlannerError(self.phase, f"destination of {mv} taken while avoiding repetition")
            return self.play(side, mv, _retry=_retry - 1)
        if mv not in self.eng.legal():
            raise PlannerError(self.phase, f"illegal move {mv} for {side}")
        self.eng.move(mv)
        self.moves.append(mv)
        if len(self.moves) > MAX_PLIES:
            raise PlannerError(self.phase, "too many plies")
        self.sync()
        st = self.state()
        if st in self.seen:
            raise Repetition(f"{self.phase}: repetition after {mv}")
        self.seen.add(st)

    def do(self, side, mv, capture=False):
        """Play mv for side, letting the other side wait as needed."""
        while self.turn != side:
            self.wait(self.turn)
        if not capture and usi_squares(mv)[-1] in self.board:
            raise PlannerError(self.phase, f"destination of {mv} was taken by a waiting move")
        self.play(side, mv)

    def perturb(self, side, exclude_sq):
        legal = self.eng.legal()
        for sq, (c, role) in self.board.items():
            if c != side or role not in REVERSIBLE or sq == exclude_sq or sq in self.reserved or sq in self.protected:
                continue
            for t in single_moves(self.board, sq):
                if t in self.board or t in self.reserved:
                    continue
                mv = usi(sq, t)
                if mv not in legal:
                    continue
                nb = dict(self.board)
                nb[t] = nb.pop(sq)
                if (frozenset(nb.items()), OTHER[side], None) in self.seen:
                    continue
                self.play(side, mv, _retry=0)
                self.pending[side].append(usi(t, sq))
                return
        raise PlannerError(self.phase, f"no perturbation available for {side}")

    def wait(self, side):
        if self.pending[side]:
            mv = self.pending[side].pop()
            a, b = usi_squares(mv)
            if a in self.protected or b in self.reserved:
                self.pending[side].insert(0, mv)   # the piece is in use: later
            elif mv in self.eng.legal() and b not in self.board:
                nb = dict(self.board)
                nb[b] = nb.pop(a)
                if (frozenset(nb.items()), OTHER[side], None) not in self.seen:
                    self.play(side, mv)
                    return
                self.pending[side].append(mv)      # try again later
        lion = self.lion_sq(side)
        legal = None
        board_key = frozenset(self.board.items())
        if lion and (board_key, OTHER[side], None) not in self.seen:
            legal = self.eng.legal()
            for m in self.adjacent_empty(lion):
                mv = usi(lion, lion, mid=m)
                if mv in legal:
                    self.play(side, mv)
                    return
        if legal is None:
            legal = self.eng.legal()
        for sq, (c, role) in self.board.items():
            if c != side or role not in REVERSIBLE:
                continue
            if sq in self.reserved or sq in self.protected:
                continue
            for t in single_moves(self.board, sq):
                if t in self.board or t in self.reserved:
                    continue
                mv = usi(sq, t)
                if mv not in legal:
                    continue
                nb = dict(self.board)
                nb[t] = nb.pop(sq)
                if (frozenset(nb.items()), OTHER[side], None) in self.seen:
                    continue
                self.play(side, mv)
                self.pending[side].append(usi(t, sq))
                return
        raise PlannerError(self.phase, f"no waiting move for {side}")

    # --- board helpers ------------------------------------------------------
    def lion_sq(self, side):
        for sq, p in self.board.items():
            if p == (side, "N"):
                return sq
        return None

    def adjacent_empty(self, sq):
        return [t for t in SQUARES if cheb(t, sq) == 1 and t not in self.board]

    def pieces(self, side, role=None):
        return [sq for sq, (c, r) in self.board.items() if c == side and (role is None or r == role)]

    def empty_squares(self):
        return [s for s in SQUARES if s not in self.board]

    # --- routing --------------------------------------------------------------
    def route(self, sq, goals, capture=False, promote=False, walls=frozenset(), depth=0):
        """Move the piece on sq to one of goals along empty squares.  Pieces in
        the way that are not confined are displaced (once).  Returns the square."""
        if sq not in self.board:
            raise PlannerError(self.phase, f"no piece on {sq} to route")
        self.protected.add(sq)
        res = None
        try:
            res = self._route(sq, goals, capture, promote, walls, depth)
            return res
        finally:
            self.protected.discard(sq)
            if res is not None:
                self.protected.discard(res)

    def _route(self, sq, goals, capture, promote, walls, depth):
        side = self.board[sq][0]
        p = path(self.board, sq, goals, walls, capture=capture)
        if p is None:
            if depth >= 2:
                raise PlannerError(self.phase, f"no route for {self.board[sq]} from {sq} to {sorted(goals)[:3]}")
            # plan through movable pieces, then displace them
            ghost = {s: p_ for s, p_ in self.board.items()
                     if s == sq or self.is_wall(p_[1]) or s in walls or (capture and s in goals)}
            p = path(ghost, sq, goals, walls, capture=capture)
            if p is None:
                raise PlannerError(self.phase, f"no route (even through movable pieces) for {self.board[sq]} from {sq}")
            crossed, cur = [], sq
            for t in p:
                crossed += traversed(self.board[sq], cur, t) + [t]
                cur = t
            avoid = set(crossed) | {sq}
            for s in crossed:
                if s in self.board and s != sq and not (capture and s in goals):
                    self.displace(s, avoid, busy=frozenset({sq}))
            if sq not in self.board:
                raise PlannerError(self.phase, "routed piece was displaced")
            return self.route(sq, goals, capture, promote, walls, depth + 1)
        cur = sq
        self.reserved = set(p)
        try:
            for i, t in enumerate(p):
                if t in self.board and not (capture and i == len(p) - 1):
                    # someone moved in meanwhile (a waiting move): re-route
                    self.reserved = set()
                    return self.route(cur, goals, capture, promote, walls, depth)
                last = i == len(p) - 1
                self.do(side, usi(cur, t, promote=promote and last), capture=capture and last)
                self.protected.discard(cur)
                cur = t
                self.protected.add(cur)
        except PlannerError as e:
            self.protected.discard(cur)
            self.reserved = set()
            if e.at is None:
                e.at = cur
            raise
        self.reserved = set()
        return cur

    def displace(self, sq, avoid, depth=0, busy=frozenset(), _replans=0, _frees=0):
        """Move the (non-confined) piece on sq to some empty square outside avoid.
        If it cannot move, make room by displacing its neighbours first."""
        if _replans > 12:
            raise PlannerError(self.phase, f"cannot displace {self.board.get(sq)} from {sq} (path keeps closing)")
        if _frees > 60:         # frontier squares freed and retried; was a RecursionError
            raise PlannerError(self.phase, f"cannot displace {self.board.get(sq)} from {sq} (frontier loop)")
        side, role = self.board[sq]
        if self.is_wall(role):
            raise PlannerError(self.phase, f"cannot displace {self.board[sq]} on {sq}")
        goals = [s for s in self.empty_squares() if s not in avoid]
        # never park a piece on a square it could not leave again (a whale on a1
        # behind the lance on a2 is immobile for the rest of the game)
        piece = self.board[sq]
        mobile = []
        for s in (goals if self.park else []):
            after = dict(self.board)
            del after[sq]
            after[s] = piece
            if any(t not in after for t in single_moves(after, s)):
                mobile.append(s)
        if mobile:
            goals = mobile
        goals.sort(key=lambda s: (s in self.target, cheb(s, sq)))
        free = [s for s in goals if s not in self.target]
        p = path(self.board, sq, set(free[:40]), walls=frozenset(avoid - {sq})) if free else None
        if p is None:
            p = path(self.board, sq, set(goals[:60]), walls=frozenset(avoid - {sq}))
        if p is None:
            p = path(self.board, sq, set(goals))
        if p is None:
            if depth >= 6:
                raise PlannerError(self.phase, f"cannot displace {self.board[sq]} from {sq}")
            # free a square on the boundary of the region it can reach, then retry
            for t in self.frontier(sq):
                if t in self.board and not self.is_wall(self.board[t][1]) and t not in busy:
                    try:
                        self.displace(t, avoid | {sq}, depth + 1, busy | {sq})
                    except PlannerError:
                        continue
                    if sq not in self.board:
                        raise PlannerError(self.phase, "displaced piece vanished")
                    return self.displace(sq, avoid, depth, busy, _replans, _frees + 1)
            raise PlannerError(self.phase, f"cannot displace {self.board[sq]} from {sq} (jammed)")
        cur = sq
        self.reserved = set(p) | set(avoid)
        for t in p:
            if t in self.board:
                self.reserved = set()
                return self.displace(cur, avoid, depth, busy, _replans + 1, _frees)
            self.do(side, usi(cur, t))
            cur = t
        self.reserved = set()

    def rescue_trapped(self, frm, to, segment):
        """Before a pawn/lance settles on `to`, move away any piece that would be
        left without a single move (a pocket sealed by the new wall)."""
        after = dict(self.board)
        after[to] = after.pop(frm)
        for sq, piece in list(self.board.items()):
            if sq == frm or self.is_wall(piece[1]) or sq == to or self.board.get(sq) != piece:
                continue
            after = dict(self.board)
            after[to] = after.pop(frm)
            if [t for t in single_moves(self.board, sq) if t not in self.board] and \
                    not [t for t in single_moves(after, sq) if t not in after]:
                try:
                    self.displace(sq, set(segment) | {t for t in SQUARES if cheb(t, to) <= 1},
                                  busy=frozenset({frm}))
                except PlannerError:
                    pass
                if self.board.get(frm) != after[to]:
                    raise PlannerError(self.phase, "wall piece displaced during rescue")

    def frontier(self, sq):
        """Occupied squares adjacent (by this piece's moves) to the region the
        piece on sq can reach through empty squares, nearest first."""
        piece = self.board[sq]
        region, stack = {sq}, [sq]
        b = dict(self.board)
        del b[sq]
        while stack:
            cur = stack.pop()
            for t in single_moves(b, cur, piece):
                if t not in b and t not in region:
                    region.add(t)
                    stack.append(t)
        out = {}
        for cur in region:
            for t in adjacent_dests(cur, piece):
                if t in self.board and t != sq:
                    out[t] = min(out.get(t, 99), cheb(t, sq))
        return sorted(out, key=out.get)

    def into_zone(self, sq, tries=0, cls=None):
        """Route the piece on sq into the enemy zone, entering from outside, and
        promote on entry.  Chooses a (staging, entry) pair whose line of entry
        is blocked only by movable pieces, displaces those, routes to the
        staging square and enters."""
        if sq not in self.board:
            raise PlannerError(self.phase, f"no piece on {sq} to promote")
        side, role = self.board[sq]
        if tries > 5:
            raise PlannerError(self.phase, f"cannot bring {self.board[sq]} at {sq} into the zone")
        if in_zone(side, sq):                      # must leave and re-enter
            out = [s for s in self.empty_squares() if not in_zone(side, s)]
            sq = self.route(sq, set(out))
        self.protected.add(sq)
        empty_board = {}
        best = None
        bound = role in ("B", "O", "+F")
        movable = lambda q: q not in self.board or not self.is_wall(self.board[q][1])
        for st in SQUARES:
            if in_zone(side, st) or (bound and sq_class(st) != sq_class(sq)) or not movable(st):
                continue
            for z in single_moves(empty_board, st, (side, role)):
                if not in_zone(side, z) or not movable(z) or (cls is not None and sq_class(z) != cls):
                    continue
                crossed = traversed((side, role), st, z)
                if not all(movable(c) for c in crossed):
                    continue
                blockers = sum(1 for c in crossed + [st, z] if c in self.board and c != sq)
                score = (blockers, cheb(sq, st))
                if best is None or score < best[0]:
                    best = (score, st, z, crossed)
        if best is None:
            self.protected.discard(sq)
            raise PlannerError(self.phase, f"no entry line for {self.board[sq]} at {sq}")
        _, st, z, crossed = best
        avoid = set(crossed) | {st, z}
        try:
            for c in crossed + [st, z]:
                if c in self.board and c != sq:
                    self.displace(c, avoid, busy=frozenset({sq}))
        finally:
            self.protected.discard(sq)
        if sq not in self.board:
            raise PlannerError(self.phase, "promoting piece was displaced")
        if st != sq:
            try:
                st = self.route(sq, {st}, walls=frozenset(avoid - {st}))
            except PlannerError as e:
                st = self.route(e.at or sq, {st})
        if z in self.board or any(c in self.board for c in crossed):
            return self.into_zone(st, tries + 1, cls)
        self.do(side, usi(st, z, promote=True))
        # park outside the zone so the entry hole stays open
        far = (lambda r: r <= 7) if side == "B" else (lambda r: r >= 6)
        park = [s for s in self.empty_squares() if not in_zone(side, s) and far(s[1])]
        park = park or [s for s in self.empty_squares() if not in_zone(side, s)]
        try:
            return self.route(z, set(park))
        except PlannerError:
            return z

    def capture(self, victim):
        """The enemy lion takes the piece on victim."""
        side = OTHER[self.board[victim][0]]
        lion = self.lion_sq(side)
        if lion is None:
            raise PlannerError(self.phase, f"{side} has no lion to capture {self.board[victim]} on {victim}")
        adjacent_only = self.board[victim][1] == "N"
        goals = {victim}
        if adjacent_only:
            # L1: a lion may always take an adjacent lion
            pre = [s for s in self.empty_squares() if cheb(s, victim) == 1]
            self.route(lion, set(pre))
            lion = self.lion_sq(side)
            self.do(side, usi(lion, victim), capture=True)
            return
        self.route(lion, goals, capture=True)

    # --- the plan -------------------------------------------------------------
    def run(self):
        T = self.target
        self.phase = "0-lions-out"
        self.do("B", usi((5, 3), (5, 5)))
        self.do("W", usi((6, 10), (6, 8)))

        # material bookkeeping
        tcount = Counter(T.values())
        self.phase = "A-captures"
        victims = []
        for x in range(12):
            slots = filegame.chu_file_slots(x)
            u = [0] * len(slots)
            for i, s in enumerate(slots):
                for r in range(1, 13):
                    if T.get((x, r)) == (s.colour, s.kind):
                        u[i] = r
            self.file_u = getattr(self, "file_u", {})
            self.file_u[x] = u
        if self.flag_target:
            # a confined White capturer must end its file play one square before l
            l = self.flag_target
            piece = T.get(l)
            if piece and piece[0] == "W" and piece[1] in CONFINED:
                slots = filegame.chu_file_slots(l[0])
                i = [j for j, sl in enumerate(slots) if (sl.colour, sl.kind) == piece][0]
                u = self.file_u[l[0]]
                options = [l[1] + 1] if piece[1] in ("P", "L") else [l[1] + 1, l[1] - 1]
                for r in options:
                    if 1 <= r <= 12 and r not in u:
                        u2 = list(u)
                        u2[i] = r
                        if filegame.admissible(slots, 12, 4).get(tuple(u2)) is not None:
                            self.file_u[l[0]] = u2
                            break
                else:
                    raise PlannerError(self.phase, "flag: no origin square for a confined capturer")
        assign = self.assign_promoted(tcount)       # (colour, kind) -> list of files
        for x in range(12):
            slots = filegame.chu_file_slots(x)
            for i, s in enumerate(slots):
                if self.file_u[x][i] == 0 and x not in assign.get((s.colour, s.kind), []):
                    victims.append((x, s.start))
        # free pieces: keep (target unpromoted + promoted) of each base type
        self.doomed_lions, self.last_royal, self.final_lion = [], None, False
        if self.flag_target and tcount[("B", "N")] == 1:
            self.final_lion = True                  # a second lion (promoted kirin) dies last
        for side in "BW":
            for base in ("G", "S", "C", "F", "T", "M", "V", "R", "H", "D", "B"):
                keep = tcount[(side, base)] + tcount[(side, "+" + base)]
                have = self.pieces(side, base)
                if base == "B":
                    # the surviving unpromoted bishop(s) must have the target's colour class
                    want_cls = [sq_class(q) for q, p in T.items() if p == (side, "B")]
                    have.sort(key=lambda q: sq_class(q) not in want_cls)
                    victims += have[keep:]
                    continue
                victims += sorted(have, key=lambda s: -abs(s[1] - 6.5))[: len(have) - keep]
            for uname, pname in (("O", "N"), ("X", "Q")):
                k, big = tcount[(side, uname)], tcount[(side, pname)]
                if k == 0 and big <= 1 and not (pname == "N" and side == "B" and self.final_lion and big == 1):
                    victims += self.pieces(side, uname)
                if big == 0 and pname == "N":
                    if side == "B" and self.flag_target:
                        self.final_lion = True      # dies on the last move instead
                    else:
                        self.doomed_lions.append(side)
                if big == 0 and pname == "Q":
                    victims += self.pieces(side, pname)
            kings, e = tcount[(side, "K")], tcount[(side, "E")]
            if kings == 1 and e == 0:
                victims += self.pieces(side, "E")
            if kings == 0:
                if side == "W":
                    raise PlannerError(self.phase, "White has no royal in the target")
                if e == 0:
                    victims += self.pieces(side, "E")
                    self.last_royal = "K"
                else:
                    self.last_royal = "K"
        for v in victims:
            if v in self.board:
                self.capture(v)

        self.early = set()          # (side, base) promoted by before_files(): skipped in phase C
        self.before_files(tcount)
        self.phase = "B-files"
        self.deferred = []          # (file, slot index, remaining abstract moves)
        for x in range(12):
            slots = filegame.chu_file_slots(x)
            u = self.file_u[x]
            state = tuple(u[i] if u[i] else (PROMOTED if x in assign.get((s.colour, s.kind), []) else CAPTURED)
                          for i, s in enumerate(slots))
            play = filegame.path_to(slots, 12, 4, state)
            if play is None:
                raise PlannerError(self.phase, f"file {x}: no abstract play to {state}")
            for mv in play:
                i, a, b = mv[0], mv[1], mv[2]
                if b == CAPTURED:
                    continue
                s = slots[i]
                frm, to = (x, a), (x, b)
                if self.board.get(frm) != (s.colour, s.kind):
                    raise PlannerError(self.phase, f"file {x}: expected {s} on {frm}, found {self.board.get(frm)}")
                step = 1 if b > a else -1
                segment = {(x, rr) for rr in range(min(a, b), max(a, b) + 1)}
                for r in range(a + step, b + step, step):
                    if (x, r) in self.board:
                        self.displace((x, r), segment)
                if self.defer and s.kind in WALLS and len(mv) != 4 and self.seals_entrance(to) \
                        and not any(len(m) == 4 for m in play):     # slot stays unpromoted
                    # a pawn/lance about to close the last entrance of some target
                    # piece: play the rest of this slot's moves after placement
                    self.deferred.append((x, i, [m for m in play[play.index(mv):] if m[2] != CAPTURED]))
                    break
                if s.kind in WALLS and len(mv) != 4:
                    self.rescue_trapped(frm, to, segment)
                self.reserved = set(segment)
                for r in range(a + step, b + step, step):
                    if (x, r) in self.board:
                        self.displace((x, r), segment)
                self.reserved = set(segment)
                self.do(s.colour, usi(frm, to, promote=len(mv) == 4))
                self.reserved = set()

        self.phase = "C-promotions"
        for side in "BW":
            for base in ("G", "S", "C", "F", "T", "M", "V", "R", "H", "D", "B", "E", "O", "X"):
                if (side, base) in self.early:
                    continue
                prom = PROMOTES[base]
                want = tcount[(side, prom)]
                if prom in ("N", "Q", "K"):
                    # merged roles: the native piece is alive now (a doomed lion
                    # dies in phase E), so promote only for a second one
                    if prom == "N" and side == "B" and self.final_lion:
                        want += 1
                    want = 1 if want == 2 else 0
                # nothing of these roles has been promoted before this phase
                for _ in range(want):
                    cands = self.pieces(side, base)
                    if not cands:
                        raise PlannerError(self.phase, f"no {side} {base} left to promote")
                    cands.sort(key=lambda s: -s[1] if side == "B" else s[1])
                    if base == "B":       # keep the bishop whose class the target needs
                        want_cls = [sq_class(q) for q, p in T.items() if p == (side, "B")]
                        cands.sort(key=lambda q: sq_class(q) in want_cls)
                    cls = None
                    if prom == "+F":          # a promoted leopard is colour-bound
                        have_cls = [sq_class(q) for q in self.pieces(side, "+F")]
                        want_cls = [sq_class(q) for q, p in T.items() if p == (side, "+F")]
                        for c in have_cls:
                            want_cls.remove(c)
                        cls = want_cls[0]
                    self.into_zone(cands[0], cls=cls)

        self.phase = "D-placement"
        self.fluid_ok = True
        reserved = self.reserve_capturers()
        if self.flag_target:
            reserved["flag"] = (None, self.flag_target)
        if self.last_royal:
            # the White piece that will take Black's last royal on its own target square
            opts = [q for q, p in T.items() if p[0] == "W" and p[1] not in CONFINED and p[1] != "N"]
            opts.sort(key=lambda q: -len([t for t in SQUARES if cheb(t, q) == 1 and t not in T]))
            if not opts:
                raise PlannerError(self.phase, "terminal: no White capturer")
            self.terminal_sq = opts[0]
            reserved["terminal"] = (None, self.terminal_sq)
        self.place_all(exclude=reserved)
        if self.run_deferred():
            self.place_all(exclude=reserved)

        self.phase = "E-finish"
        for side in self.doomed_lions:
            cap_sq, capturer_target = reserved[side]
            piece = self.target[capturer_target]
            cands = [q for q, p in self.board.items() if p == piece and self.target.get(q) != p]
            if not cands and self.board.get(capturer_target) == piece:
                # the capturer already sits on its square: step aside first
                for t in single_moves(self.board, capturer_target):
                    if t in self.board:
                        continue
                    b2 = dict(self.board)
                    b2[t] = b2.pop(capturer_target)
                    if capturer_target in single_moves(b2, t):
                        self.do(piece[0], usi(capturer_target, t))
                        cands = [t]
                        break
            if not cands:
                raise PlannerError(self.phase, f"capturer {piece} not found")
            cap_sq = cands[0]
            lion = self.lion_sq(side)
            if lion is None:
                raise PlannerError(self.phase, f"{side} lion already gone")
            if lion != capturer_target:
                self.route(lion, {capturer_target})
            # make sure the capturer's side is not under the counter-strike ban
            self.flush()
            if self.turn != OTHER[side]:
                self.wait(self.turn)
            self.flush()
            self.route(cap_sq, {capturer_target}, capture=True)
        if self.flag_target:
            self.place_all(exclude={"flag": (None, self.flag_target)})
            self.flag_capture()
            self.verify()
            return self.moves
        if self.last_royal:
            self.place_all(exclude={"terminal": (None, self.terminal_sq)})
            self.terminal_capture()
            self.verify()
            return self.moves
        self.place_all(exclude={})
        for _ in range(12):
            self.flush()
            if self.flag is None and self.turn == self.end_turn and not any(self.pending.values()):
                break
            self.wait(self.turn)
        self.fix_parity(want=self.end_turn)
        self.verify()
        return self.moves

    def before_files(self, tcount):
        """Hook between phases A and B (plan/mateplan.py: the second-royal shield); none here."""

    def assign_promoted(self, tcount):
        """Choose an origin file for every promoted lance/chariot/go-between."""
        assign = defaultdict(list)
        from count.candidates import chu_setup, file_features
        setup = chu_setup("file")
        elig, feats_j = {}, {}
        for x in range(12):
            feats = file_features(setup, x, tuple(self.file_u[x]), "file", True)
            if feats is None:
                raise PlannerError("A-captures", f"file {x} U-config not admissible")
            elig[x] = feats[7]
            feats_j[x] = feats[4]
        for side in "BW":
            for kind in ("L", "RC", "GB"):
                need = tcount[(side, "+" + kind)]
                files = [x for x in range(12) if elig[x].get((side, kind), 0)]
                if len(files) < need:
                    raise PlannerError("A-captures", f"not enough eligible files for {side} +{kind}")
                assign[(side, kind)] = files[:need]
        # tokins: one per file with no unpromoted pawn, Black and White exclusive (I4)
        free_files = [x for x in range(12) if feats_j[x]]
        for side in "BW":
            need = tcount[(side, "+P")]
            if len(free_files) < need:
                raise PlannerError("A-captures", f"not enough pawn-free files for {side} tokins")
            assign[(side, "P")], free_files = free_files[:need], free_files[need:]
        return assign

    def reserve_capturers(self):
        """For each doomed lion pick an enemy piece (and its target square) that
        will capture it there; those pieces are placed last."""
        reserved = {}
        for side in self.doomed_lions:
            enemy = OTHER[side]
            best = None
            for sq, (c, role) in self.board.items():
                if c != enemy or role in ("N", "K") or role in CONFINED or role in BASE:
                    continue
                tgt = self.target_for(sq)
                if tgt is None:
                    continue
                if best is None or role in ("Q", "R", "+R", "D", "+B", "H"):
                    best = (sq, tgt)
            if best is None:
                raise PlannerError("D-placement", f"no capturer available for the {side} lion")
            reserved[side] = best
        return reserved

    def target_for(self, sq):
        """A target square for the piece on sq (greedy matching, recomputed)."""
        piece = self.board[sq]
        if piece[1] in WALLS:
            return sq
        if piece[1] in FLUID_CONFINED:
            want = [s for s, p in self.target.items() if p == piece and s[0] == sq[0]]
            if len(want) != 1:
                raise PlannerError(self.phase, f"no target for {piece} on file {sq[0]}")
            return want[0]
        want = [s for s, p in self.target.items() if p == piece]
        have = [s for s, p in self.board.items() if p == piece]
        extra = 1 if (piece == ("B", "N") and self.final_lion) or (piece == ("B", "K") and self.last_royal) else 0
        if len(want) + extra != len(have):
            raise PlannerError(self.phase, f"material mismatch for {piece}: have {len(have)}, want {len(want)}")
        # greedy nearest matching, deterministic; colour-bound pieces keep their class
        bound = piece[1] in ("B", "O", "+F")
        pairs = sorted((cheb(a, b), a, b) for a in have for b in want
                       if not bound or sq_class(a) == sq_class(b))
        used_a, used_b, match = set(), set(), {}
        for _, a, b in pairs:
            if a not in used_a and b not in used_b:
                match[a] = b
                used_a.add(a)
                used_b.add(b)
        if sq not in match:
            if extra:
                return None                         # the lion that dies on the last move
            raise PlannerError(self.phase, f"no colour-consistent target for {piece} on {sq}")
        return match[sq]

    def peel_order(self, excluded_targets):
        """Insertion order of the target's movable pieces: peel the target by
        repeatedly removing a piece that could have been inserted last (its
        square can be reached by a reverse move through squares that are empty
        in the target or already peeled); when nothing can be peeled, peel the
        piece with the largest reverse region anyway and mark it (its insertion
        will go through a buffer square).  Returns [(square, needs_buffer)] in
        insertion order."""
        remaining = {sq: p for sq, p in self.target.items()
                     if p[1] not in WALLS and sq not in excluded_targets}
        obstacles = dict(self.target)
        order = []
        while remaining:
            best = None
            for sq, piece in remaining.items():
                b = dict(obstacles)
                del b[sq]
                region, stack = {sq}, [sq]
                while stack and len(region) < 40:
                    cur = stack.pop()
                    for t in reverse_moves(b, cur, piece):
                        if t not in region:
                            region.add(t)
                            stack.append(t)
                size = len(region)
                if best is None or size > best[0]:
                    best = (size, sq)
            size, sq = best
            # a small pocket is not an entrance (the piece could not get in later)
            order.append((sq, size < 12))
            del remaining[sq]
            del obstacles[sq]
        order.reverse()
        return order

    def instance_for(self, tgt, inserted, skip=frozenset()):
        """Choose the piece to put on target square tgt: nearest unplaced piece
        of that type (colour class matched for bound pieces), not in `skip`."""
        piece = self.target[tgt]
        bound = piece[1] in ("B", "O", "+F")
        cands = [q for q, p in self.board.items() if p == piece and q not in inserted and q not in skip
                 and not (bound and sq_class(q) != sq_class(tgt))]
        if piece[1] in FLUID_CONFINED:
            cands = [q for q in cands if q[0] == tgt[0]]
        if not cands:
            raise PlannerError(self.phase, f"no free instance of {piece} for {tgt}")
        return min(cands, key=lambda q: cheb(q, tgt))

    def place_all_peel(self, exclude):
        excluded_targets = {tgt for _, tgt in exclude.values()} | self.blocked_targets()
        order = self.peel_order(excluded_targets)
        inserted = set()                    # target squares holding their piece, by us
        queue = list(order)
        attempts = Counter()
        while queue:
            tgt, needs_buffer = queue.pop(0)
            if self.board.get(tgt) == self.target[tgt]:
                inserted.add(tgt)
                continue
            attempts[tgt] += 1
            if attempts[tgt] > 6:
                raise PlannerError(self.phase, f"placement did not converge at {tgt}")
            sq = self.instance_for(tgt, inserted)
            walls = frozenset(inserted)
            if tgt in self.board:               # an unplaced piece sits on the target
                try:
                    self.displace(tgt, {tgt} | walls, busy=frozenset({sq}))
                except PlannerError:
                    pass
                if tgt in self.board or self.board.get(sq) != self.target[tgt]:
                    queue.insert(min(3, len(queue)), (tgt, needs_buffer))
                    continue
            try:
                self.route(sq, {tgt}, walls=walls)
            except PlannerError as e:
                sq = e.at or sq
                if self.board.get(sq) != self.target[tgt]:
                    queue.insert(min(3, len(queue)), (tgt, needs_buffer))
                    continue
                # buffer: let inserted blockers step aside, then re-insert them
                before = set(inserted)
                try:
                    self.route(sq, {tgt})
                except PlannerError:
                    queue.insert(min(3, len(queue)), (tgt, needs_buffer))
                    continue
                for u in before:
                    if self.board.get(u) != self.target[u]:
                        inserted.discard(u)
                        queue.insert(0, (u, False))
            if self.board.get(tgt) == self.target[tgt]:
                inserted.add(tgt)
            else:
                queue.insert(min(3, len(queue)), (tgt, needs_buffer))
            # pieces knocked off their squares by waiting moves / displacements
            for u in list(inserted):
                if self.board.get(u) != self.target[u]:
                    inserted.discard(u)
                    queue.append((u, False))

    def place_all_greedy(self, exclude):
        excluded_targets = {tgt for _, tgt in exclude.values()}

        def openness(t):
            return sum(1 for u in SQUARES if cheb(u, t) == 1 and u not in self.target)

        for it in range(400):
            todo = [sq for sq in self.board if self.board[sq][1] not in WALLS
                    and not (self.board[sq][1] == "N" and self.board[sq][0] in self.doomed_lions)
                    and self.target_for(sq) != sq]
            todo = [sq for sq in todo if not (self.board[sq][1] == "N" and self.board[sq][0] in self.doomed_lions)]
            blocked = self.blocked_targets()
            todo = [sq for sq in todo if self.target_for(sq) is not None
                    and self.target_for(sq) not in excluded_targets and self.target_for(sq) not in blocked]
            if not todo:
                return
            if it < 3:
                todo.sort(key=lambda sq: openness(self.target_for(sq)))
            else:                      # break displacement cycles
                self.rng.shuffle(todo)
            progressed = False
            todo = [(sq, self.board[sq]) for sq in todo]
            for sq, piece in todo:
                if self.board.get(sq) != piece:
                    continue                       # moved meanwhile
                tgt = self.target_for(sq)
                if tgt == sq or tgt is None:
                    continue
                placed = frozenset(u for u, p in self.board.items()
                                   if self.target.get(u) == p and p[1] not in WALLS and u != tgt)
                if tgt in self.board:
                    if self.board[tgt][1] in WALLS:
                        raise PlannerError(self.phase, f"target {tgt} holds a confined piece")
                    try:
                        self.displace(tgt, {tgt} | placed, busy=frozenset({sq}))
                    except PlannerError:
                        continue
                    if sq not in self.board:
                        continue
                try:
                    self.route(sq, {tgt}, walls=placed)
                    progressed = True
                except PlannerError as e:
                    sq = e.at or sq
                    if self.board.get(sq) != piece:
                        continue
                    try:
                        self.route(sq, {tgt})
                        progressed = True
                    except PlannerError:
                        continue
            if not progressed:
                sq = [q for q, _ in todo if q in self.board and self.board[q][1] not in WALLS
                      and self.target_for(q) not in (q, None)]
                if not sq:
                    continue
                self.route(sq[0], {self.target_for(sq[0])})   # raises with the reason
        raise PlannerError(self.phase, "placement did not converge")

    def seals_entrance(self, sq):
        """Would a wall on sq leave some non-wall target piece without any
        entrance in the final configuration?  sq may be the wall's own final
        square (a pawn settling on f2 behind a whale on f1 seals it just as an
        intermediate square would; before 2026-10-06 final squares were skipped)."""
        for t, piece in self.target.items():
            if piece[1] in WALLS or cheb(t, sq) > 2:
                continue
            final = {q: p for q, p in self.target.items() if q != t and q != sq}
            if sq in reverse_moves(final, t, piece):
                final[sq] = ("W", "P")
                if not reverse_moves(final, t, piece):
                    return True
        return False

    def run_deferred(self):
        """Play the deferred pawn/lance moves (after placement)."""
        done = False
        for x, i, moves in self.deferred:
            slots = filegame.chu_file_slots(x)
            for mv in moves:
                sl = slots[mv[0]]           # the rest of the file's play may involve other slots
                a, b = mv[1], mv[2]
                frm, to = (x, a), (x, b)
                if self.board.get(frm) != (sl.colour, sl.kind):
                    raise PlannerError(self.phase, f"deferred: expected {sl} on {frm}")
                step = 1 if b > a else -1
                segment = {(x, rr) for rr in range(min(a, b), max(a, b) + 1)}
                self.reserved = set(segment)
                for r in range(a + step, b + step, step):
                    if (x, r) in self.board:
                        self.displace((x, r), segment, busy=frozenset({frm}))
                self.reserved = set(segment)
                self.do(sl.colour, usi(frm, to, promote=len(mv) == 4))
                self.reserved = set()
                done = True
        self.deferred = []
        return done

    def blocked_targets(self):
        """Target squares currently held by a wall piece (freed by deferred moves)."""
        return {t for t in self.target if t in self.board and self.is_wall(self.board[t][1])
                and self.board[t] != self.target[t]}

    def entrances(self, tgt, piece, inserted):
        """Squares from which `piece` could move onto tgt now, excluding
        squares held by inserted pieces or by walls."""
        b = {q: p for q, p in self.board.items() if q in inserted or self.is_wall(p[1])}
        b.pop(tgt, None)
        return [a for a in reverse_moves(b, tgt, piece) if a not in inserted]

    def place_all_edge(self, exclude):
        """Most-constrained-first insertion: repeatedly insert the piece whose
        target square has the fewest entrances given the pieces inserted so far
        (home-rank corners of whales, white horses, coppers, silvers first); a
        piece with no entrance left goes in through a buffer (inserted blockers
        step aside and are re-inserted)."""
        excluded_targets = {tgt for _, tgt in exclude.values()}
        targets = [sq for sq, p in self.target.items() if p[1] not in WALLS and sq not in excluded_targets]
        inserted = set()
        attempts = Counter()
        while True:
            blocked = self.blocked_targets()
            todo = [t for t in targets if self.board.get(t) != self.target[t] and t not in blocked]
            inserted = {t for t in targets if self.board.get(t) == self.target[t]}
            if not todo:
                return
            scored = []
            for t in todo:
                ent = self.entrances(t, self.target[t], inserted)
                scored.append((len(ent) == 0, len(ent), t))
            scored.sort()
            # prefer the most constrained square that still has an entrance
            _, nent, tgt = scored[0]
            attempts[tgt] += 1
            if attempts[tgt] > 8:
                raise PlannerError(self.phase, f"placement did not converge at {tgt}")
            try:
                sq = self.instance_for(tgt, inserted)
            except PlannerError:
                raise
            walls = frozenset(inserted)
            if tgt in self.board:
                try:
                    self.displace(tgt, {tgt} | walls, busy=frozenset({sq}))
                except PlannerError:
                    pass
                if tgt in self.board or self.board.get(sq) != self.target[tgt]:
                    continue
            try:
                self.route(sq, {tgt}, walls=walls)
            except PlannerError as e:
                sq = e.at or sq
                if self.board.get(sq) != self.target[tgt]:
                    continue
                try:
                    self.route(sq, {tgt})          # through a buffer: inserted blockers step aside
                except PlannerError:
                    continue

    def approach(self, tgt, piece, inserted, cap=40):
        """Squares from which `piece` can still approach tgt by reverse moves
        through squares not held by walls or inserted pieces (the inserted
        pieces count as standing on their target squares).  Capped at `cap`."""
        b = {q: p for q, p in self.board.items() if self.is_wall(p[1])}
        for q in inserted:
            b[q] = self.target[q]
        b.pop(tgt, None)
        region, stack = {tgt}, [tgt]
        while stack and len(region) <= cap:
            cur = stack.pop()
            for t in reverse_moves(b, cur, piece):
                if t not in region and t not in inserted:
                    region.add(t)
                    stack.append(t)
        region.discard(tgt)
        return region

    OPEN = 12       # an approach region smaller than this is a pocket: insert now or never

    def place_all_deps(self, exclude):
        """Dependency-aware insertion.  Each step inserts one target piece: a
        piece whose approach region (`approach`) has become a pocket goes in
        first (now or never); otherwise the piece whose insertion closes the
        fewest other approach regions, most constrained first, edge squares
        first.  Fixes the edge-first failures where pieces inserted early on a
        whale's / horse's only file sealed the corner square."""
        excluded_targets = {tgt for _, tgt in exclude.values()}
        targets = [sq for sq, p in self.target.items() if p[1] not in WALLS and sq not in excluded_targets]
        attempts = Counter()
        while True:
            blocked = self.blocked_targets()
            inserted = {t for t in targets if self.board.get(t) == self.target[t]}
            todo = [t for t in targets if t not in inserted and t not in blocked]
            if not todo:
                return
            regions = {t: self.approach(t, self.target[t], inserted) for t in todo}
            scored = []
            for t in todo:
                r = len(regions[t])
                if r == 0:
                    scored.append((3, 0, 0, 0, t))         # sealed: last resort, goes through a buffer
                    continue
                closes = 0
                for u in todo:
                    if u != t and t in regions[u] and len(regions[u]) >= self.OPEN:
                        if len(self.approach(u, self.target[u], inserted | {t})) < self.OPEN:
                            closes += 1
                urgent = 0 if r < self.OPEN else 1
                edge = min(t[0], 11 - t[0], t[1] - 1, 12 - t[1])
                scored.append((urgent, closes, r, edge, t))
            scored.sort()
            tgt = scored[0][-1]
            attempts[tgt] += 1
            if attempts[tgt] > 8:
                raise PlannerError(self.phase, f"placement did not converge at {tgt}")
            skip = set()
            for _ in range(3):                      # up to three instances of the piece
                try:
                    sq = self.instance_for(tgt, inserted, skip=frozenset(skip))
                except PlannerError:
                    if not skip:
                        raise
                    break
                skip.add(sq)
                walls = frozenset(inserted)
                if tgt in self.board:
                    try:
                        self.displace(tgt, {tgt} | walls, busy=frozenset({sq}))
                    except PlannerError:
                        pass
                    if tgt in self.board or self.board.get(sq) != self.target[tgt]:
                        break
                try:
                    self.route(sq, {tgt}, walls=walls)
                    break
                except PlannerError as e:
                    at = e.at or sq
                    if self.board.get(at) != self.target[tgt]:
                        break                       # the board changed under us: rescore
                    try:
                        self.route(at, {tgt})       # through a buffer: inserted blockers step aside
                        break
                    except PlannerError as e2:
                        if e2.at is None and "no route" in e2.reason:
                            continue                # this instance cannot get there at all: try another
                        break

    def place_all(self, exclude):
        """Greedy placement (openness order, displacement, cycle breaking by
        reshuffling) or peeling order (baseline, by seed parity); edge-first
        or dependency-aware insertion as explicit fallback strategies."""
        if self.strategy == "greedy":
            return self.place_all_greedy(exclude)
        if self.strategy == "edge":
            return self.place_all_edge(exclude)
        if self.strategy == "deps":
            return self.place_all_deps(exclude)
        return self.place_all_peel(exclude)

    def terminal_capture(self):
        """The target has no Black royal: White's capture of it is the last move."""
        royals = [q for q in self.pieces("B", "K") if self.target_for(q) is None]
        if len(royals) != 1:
            raise PlannerError(self.phase, f"expected one Black royal left, found {len(royals)}")
        k = royals[0]
        s_r = self.terminal_sq
        piece = self.target[s_r]
        caps = [q for q, p in self.board.items() if p == piece and self.target.get(q) != p]
        if not caps and self.board.get(s_r) == piece:
            for t in single_moves(self.board, s_r):
                if t in self.board:
                    continue
                b2 = dict(self.board)
                b2[t] = b2.pop(s_r)
                if s_r in single_moves(b2, t):
                    self.do("W", usi(s_r, t))
                    caps = [t]
                    break
        if not caps:
            raise PlannerError(self.phase, "terminal: capturer not found")
        cap = caps[0]
        if s_r in self.board and s_r != k:
            self.displace(s_r, {s_r}, busy=frozenset({cap, k}))
        if k != s_r:
            self.route(k, {s_r}, walls=frozenset({cap}))
        origins = []
        for a in SQUARES:
            if a in self.board and a != cap:
                continue
            probe = dict(self.board)
            probe.pop(cap, None)
            probe[a] = piece
            if s_r in single_moves(probe, a, piece):
                origins.append(a)
        if self.forced_origin is not None:
            origins = [a for a in origins if a == self.forced_origin]
        if not origins:
            raise PlannerError(self.phase, "terminal: no origin square for the capturer")
        if cap not in origins:
            cap = self.route(cap, set(origins))
        # routing may have displaced placed pieces: put them back, then re-check
        self.place_all(exclude={"terminal": (None, s_r)})
        if self.board.get(s_r) != ("B", "K") or self.board.get(cap) != piece or s_r not in single_moves(self.board, cap):
            raise PlannerError(self.phase, "terminal: setup disturbed by re-placement")
        self.flush()
        self.fix_parity(want="W")
        if s_r not in single_moves(self.board, cap):
            raise PlannerError(self.phase, "terminal: capture no longer possible")
        self.play("W", usi(cap, s_r))

    def flag_capture(self):
        """Flag-on certificate: the extra Black lion goes to l, the White piece
        of the target on l comes to an origin square, and takes it last."""
        l = self.flag_target
        piece = self.target.get(l)
        if piece is None or piece[0] != "W" or piece[1] == "N":
            raise PlannerError(self.phase, f"flag square {l} is not a White non-lion in the target")
        lions = [q for q, p in self.board.items() if p == ("B", "N") and self.target_for(q) is None]
        if len(lions) != 1:
            raise PlannerError(self.phase, f"expected one extra Black lion, found {len(lions)}")
        caps = [q for q, p in self.board.items() if p == piece and self.target.get(q) != p]
        if not caps and self.board.get(l) == piece:
            for t in single_moves(self.board, l):      # step aside, keeping l in reach
                if t in self.board:
                    continue
                b2 = dict(self.board)
                b2[t] = b2.pop(l)
                if l in single_moves(b2, t):
                    self.do("W", usi(l, t))
                    caps = [t]
                    break
        if not caps:
            raise PlannerError(self.phase, "flag: capturer not found")
        cap = caps[0]
        if l in self.board and self.board[l] != ("B", "N"):
            self.displace(l, {l}, busy=frozenset({cap, lions[0]}))
        if lions[0] != l:
            self.route(lions[0], {l}, walls=frozenset({cap}))
        origins = []
        for a in SQUARES:
            if a in self.board and a != cap:
                continue
            probe = dict(self.board)
            probe.pop(cap, None)
            probe[a] = piece
            if l in single_moves(probe, a, piece):
                origins.append(a)
        if self.forced_origin is not None:
            origins = [a for a in origins if a == self.forced_origin]
        if not origins:
            raise PlannerError(self.phase, "flag: no origin square for the capturer")
        if cap not in origins:
            if piece[1] in CONFINED:
                raise PlannerError(self.phase, "flag: confined capturer not on its origin")
            cap = self.route(cap, set(origins))
        self.place_all(exclude={"flag": (None, l)})
        if self.board.get(l) != ("B", "N") or self.board.get(cap) != piece or l not in single_moves(self.board, cap):
            raise PlannerError(self.phase, "flag: setup disturbed by re-placement")
        self.flush()
        self.fix_parity(want="W")
        if l not in single_moves(self.board, cap):
            raise PlannerError(self.phase, "flag: capture no longer possible")
        self.play("W", usi(cap, l))

    def flush(self):
        for _ in range(10):
            if not any(self.pending.values()):
                return
            for side in "BW":
                if self.pending[side]:
                    mv = self.pending[side].pop()
                    a, b = usi_squares(mv)
                    if b in self.board or self.board.get(a) is None or a in self.protected:
                        continue                       # piece gone, square taken or in use: drop
                    while self.turn != side:
                        self.wait(self.turn)
                    nb = dict(self.board)
                    nb[b] = nb.pop(a)
                    if (frozenset(nb.items()), OTHER[side], None) in self.seen:
                        self.wait(side)                # some other waiting move first
                        self.pending[side].append(mv)
                        continue
                    self.do(side, mv)
        raise PlannerError(self.phase, "could not flush waiting moves")

    def fix_parity(self, want="B"):
        if self.turn == want:
            return
        side = self.turn
        lion = self.lion_sq(side)
        if lion:
            for m in self.adjacent_empty(lion):
                mv = usi(lion, lion, mid=m)
                if mv in self.eng.legal():
                    self.play(side, mv)
                    return
        # a 3-cycle with a king-mover and a 2-cycle for the other side
        for sq, (c, role) in list(self.board.items()):
            if c != side or role not in ("K", "Q"):
                continue
            emp = self.adjacent_empty(sq)
            for a in emp:
                for b in emp:
                    if cheb(a, b) == 1 and a != b:
                        self.play(side, usi(sq, a))
                        self.wait(OTHER[side])
                        self.play(side, usi(a, b))
                        self.flush()
                        if self.turn != side:
                            self.wait(OTHER[side])
                        self.play(side, usi(b, sq))
                        self.flush()
                        return
        raise PlannerError(self.phase, f"cannot fix parity for {side}")

    def verify(self):
        if self.turn != self.end_turn or self.flag != self.flag_target:
            raise PlannerError("verify", f"ends with {self.turn} to move, flag {self.flag}")
        if self.board != self.target:
            diff = [(s, self.board.get(s), self.target.get(s)) for s in SQUARES
                    if self.board.get(s) != self.target.get(s)]
            raise PlannerError("verify", f"board differs on {len(diff)} squares, e.g. {diff[:3]}")


