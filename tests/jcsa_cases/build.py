#!/usr/bin/env python3
"""Build the JCSA rule-difference test positions (docs/jcsa-delta.md, docs/jcsa-rules-en.md).

Each case embeds a JCSA diagram (or a constructed position) in a full legal
position with both royals, states the side to move and the counter-strike
field, names the tested move and records its verdict under lishogi (checked
against the engine) and under JCSA (checked against src/jcsa where the layer
implements the rule, otherwise the expected verdict from the text).

Usage: python3 tests/jcsa_cases/build.py   -> cases.json, README.md (ASCII boards)
Diagram coordinates: JCSA file f (1 = rightmost) and rank r (1 = top, White's side)
map to our (x, y) = (12 - f, 13 - r).
"""
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
sys.path.insert(0, str(ROOT / "src"))
from count.sampler import to_sfen                                   # noqa: E402
from plan.engine import Engine                                      # noqa: E402
from plan.moves import ascii_board, usi, usi_sq, usi_squares         # noqa: E402
from jcsa.mode import legal_moves as jcsa_legal                      # noqa: E402

ENG = Engine()
IMG = "refs/rules/jcsa/original/www.chushogi-renmei.com/kouza/"


def J(f, r):
    """JCSA diagram square -> board square."""
    return (12 - f, 13 - r)


def sfen(board, turn, flag):
    return to_sfen(board, "b" if turn == "B" else "w", usi_sq(flag) if flag else "-")


def lishogi_legal(board, turn, flag):
    ENG.position(sfen(board, turn, flag))
    return ENG.legal()


def status(board, turn, flag=None):
    ENG.position(sfen(board, turn, flag))
    return ENG.status()


def moves_landing(moves, frm, to):
    return sorted(m for m in moves if usi_squares(m)[0] == frm and usi_squares(m)[-1] == to)


def apply(board, mv):
    """Board after a USI move (captures on every named square; '+' promotes)."""
    sqs = usi_squares(mv)
    b = dict(board)
    piece = b.pop(sqs[0])
    for s in sqs[1:]:
        b.pop(s, None)
    if mv.endswith("+"):
        role = piece[1]
        piece = (piece[0], {"L": "+L", "P": "+P", "GB": "+GB", "O": "N", "X": "Q", "E": "K"}.get(role, "+" + role))
    b[sqs[-1]] = piece
    return b


cases = []


def case(cid, source, image, text_ref, description, board, turn, flag, move, lishogi, jcsa, layer, note="", sfen_text=None):
    """sfen_text: the SFEN to record instead of the merged-role rendering (e.g. the engine's own
    SFEN keeping a promoted kirin as +o, which a position reached by a kirin's capture must show)."""
    moves = lishogi_legal(board, turn, flag)
    if move is None:
        l_verdict = status(board, turn, flag)
        j_layer = None
    else:
        frm, to = usi_squares(move)[0], usi_squares(move)[-1]
        if move.endswith("?"):                       # any legal way from frm to to
            cand = moves_landing(moves, frm, to)
            l_verdict = "legal" if cand else "illegal"
            move_str = f"{usi_sq(frm)}->{usi_sq(to)} (any route)"
            jl = jcsa_legal(ENG, board, turn, flag) if layer in ("counter-strike", "promotion") else None
            j_layer = None if jl is None else ("legal" if moves_landing(jl, frm, to) else "illegal")
        else:
            l_verdict = "legal" if move in moves else "illegal"
            move_str = move
            jl = jcsa_legal(ENG, board, turn, flag) if layer in ("counter-strike", "promotion") else None
            j_layer = None if jl is None else ("legal" if move in jl else "illegal")
    ok_l = (l_verdict == lishogi)
    ok_j = (j_layer is None) or (j_layer == jcsa)
    rec = dict(id=cid, source=source, image=image, text_ref=text_ref, description=description,
               sfen=(sfen_text or sfen(board, turn, flag)), side_to_move=turn, counter_strike=usi_sq(flag) if flag else "-",
               move=(move_str if move else "(status)"), verdict_lishogi=lishogi, verdict_lishogi_engine=l_verdict,
               verdict_jcsa=jcsa, verdict_jcsa_layer=(j_layer or f"not implemented ({layer})"),
               difference=(lishogi != jcsa), note=note, ascii=ascii_board(board))
    cases.append(rec)
    flag_s = "" if ok_l and ok_j else "   <-- MISMATCH"
    print(f"{cid}: lishogi {lishogi}/{l_verdict}  JCSA {jcsa}/{j_layer or '-'}{flag_s}")
    return rec


K, k, N, n = ("B", "K"), ("W", "K"), ("B", "N"), ("W", "N")
KINGS = {(0, 1): K, (0, 12): k}      # a1 Black king, a12 White king: far from every diagram

# --- rule.htm / rule2007.htm diagrams (lion rules; same under both rule sets) ---
b = dict(KINGS); b.update({J(6, 5): N, J(6, 9): ("B", "R"), J(4, 4): n, J(1, 1): ("W", "B")})
case("C01", "rule2007 七.二 (rule.htm 5.二)", "rule/image001.gif", "L-2", "lion foot: both lions at distance two, each protected (rook / bishop); neither lion may take the other",
     b, "B", None, usi(J(6, 5), J(4, 4)) + "?", "illegal", "illegal", "engine", "same under both (L1)")
case("C01w", "rule2007 七.二", "rule/image001.gif", "L-2", "same, White to move", b, "W", None, usi(J(4, 4), J(6, 5)) + "?", "illegal", "illegal", "engine")

b = dict(KINGS); b.update({J(1, 1): N, J(3, 3): n, J(7, 7): ("B", "B"), J(3, 9): ("W", "R")})
case("C02", "rule2007 七.三", "rule/image002.gif", "L-3", "ura-ashi: Black bishop 7七 protects the Black lion 1一 through the White lion 3三; White lion may not take it",
     b, "W", None, usi(J(3, 3), J(1, 1)) + "?", "illegal", "illegal", "engine", "same under both (L1 X-ray)")
b2 = dict(b); del b2[J(7, 7)]
case("C02b", "rule2007 七.三", "rule/image002.gif", "L-3", "same without the bishop: the unprotected Black lion may be taken",
     b2, "W", None, usi(J(3, 3), J(1, 1)) + "?", "legal", "legal", "engine")

b = dict(KINGS); b.update({J(3, 2): N, J(2, 2): ("W", "S"), J(1, 1): n, J(5, 4): ("B", "B"), J(1, 5): ("W", "R")})
mv = usi(J(3, 2), J(1, 1), mid=J(2, 2))
case("C03", "rule2007 七.五", "rule/image004.gif", "L-5", "tsukegui (kuisoe): Black lion takes the silver 2二 and the protected White lion 1一 in one move",
     b, "B", None, mv, "legal", "legal", "engine", "same under both (L2)")
b3 = apply(b, mv)
case("C03b", "rule2007 七.五", "rule/image004.gif", "L-5", "after the tsukegui, White's rook 1五 'strikes the lion' at once (lion took lion: no counter-strike ban)",
     b3, "W", None, usi(J(1, 5), J(1, 1)), "legal", "legal", "counter-strike")

# --- 先獅子 / counter-strike: the difference ---
b = dict(KINGS); b.update({J(7, 5): N, J(7, 6): ("B", "G"), J(6, 6): ("B", "B"), J(1, 1): n, J(7, 1): ("W", "R"), J(1, 5): ("W", "R")})
mv = usi(J(6, 6), J(1, 1))
case("C04", "rule2007 七.四", "rule/image003.gif", "L-4", "sakishishi: both lions attacked by non-lions; Black bishop 6六 takes the White lion 1一 (always allowed)",
     b, "B", None, mv, "legal", "legal", "counter-strike")
b4 = apply(b, mv)
case("C04a", "rule2007 七.四", "rule/image003.gif", "L-4", "next move: White rook 7一 may not take the Black lion 7五 (lishogi: flag on 1一; JCSA: Black's lion has a foot, gold 7六)",
     b4, "W", J(1, 1), usi(J(7, 1), J(7, 5)), "illegal", "illegal", "counter-strike")
case("C04c", "rule2007 七.四", "rule/image003.gif", "L-4", "next move: White rook 1五 recaptures the bishop on 1一 (allowed under both)",
     b4, "W", J(1, 1), usi(J(1, 5), J(1, 1)), "legal", "legal", "counter-strike")
b5 = dict(b4); del b5[J(7, 6)]
case("C04b", "rule_hosoku2004 3.⑥ (rule2007 七.四)", "rule/image003.gif", "L-4, H-3.6", "DIFFERENCE: same but the Black lion has no foot (no gold 7六): lishogi still bans the rook's capture; JCSA's sakishishi applies only when the capturing side's lion has a foot, so White may take it",
     b5, "W", J(1, 1), usi(J(7, 1), J(7, 5)), "illegal", "legal", "counter-strike", "the 'Okazaki rule' as applied by the Federation since 2004")

# --- promoted kirin on the capture square (R-L4, kirin sentence; constructed) ---
# Built by playing the kirin's capture-with-promotion in the engine: White kirin f5 takes the
# Black lion e4 and promotes (7h8i+ in USI), the engine sets the flag on e4.
from count.sfen import parse as _parse
for cid, extra, lverdict, jverdict, desc in (
        ("C17", {(4, 3): ("W", "G")}, "legal", "illegal", "DIFFERENCE: a kirin took a lion and promoted; the new lion on the capture square has a foot (gold e3). lishogi exempts the capture square, so the Black rook may take it back; JCSA's sakishishi covers the promoted kirin like any lion: banned"),
        ("C17b", {}, "legal", "legal", "same without the gold: the new lion has no foot, so the recapture is allowed under both")):
    P = dict(KINGS); P.update({(4, 4): ("B", "N"), (5, 5): ("W", "O"), (4, 9): ("B", "R")}); P.update(extra)
    ENG.position(to_sfen(P, "w"), [usi((5, 5), (4, 4), promote=True)])
    engine_sfen = ENG.sfen()                       # keeps the promoted kirin as +o (a lion's own capture never sets the flag)
    bT, _, fT = _parse(engine_sfen)
    case(cid, "rule2007 七.四 last sentence (kirin capturing a lion and promoting establishes sakishishi)", "(constructed, played through the engine)", "R-L4", desc,
         bT, "B", fT, usi((4, 9), (4, 4)), lverdict, jverdict, "counter-strike", "second genuine sakishishi difference: lishogi exempts the capture square; the piece on the capture square is the promoted kirin (+o)", sfen_text=engine_sfen)

# --- hit-and-run by an eagle (constructed; no JCSA diagram) ---
b = dict(KINGS); b.update({(5, 8): ("W", "+D"), (4, 7): N, (3, 6): ("B", "G"), (10, 2): ("B", "R")})
case("C05", "rule2007 七.四 (取り返す), spec.md §4 L3 quirk", "(constructed)", "L-4", "DIFFERENCE: during the ban (flag on 11k where a White lion was just taken), White's soaring eagle igui-captures the protected Black lion on its mid square: lishogi tests only the destination (allowed); JCSA bans every recapture of the lion",
     b, "W", (10, 2), usi((5, 8), (5, 8), mid=(4, 7)), "legal", "illegal", "counter-strike", "the flag square holds the Black rook that took the lion")
case("C05b", "rule2007 七.四", "(constructed)", "L-4", "DIFFERENCE: same, pass-through capture (eagle takes the lion on 4,7 and the gold on 3,6)",
     b, "W", (10, 2), usi((5, 8), (3, 6), mid=(4, 7)), "legal", "illegal", "counter-strike")
b6 = dict(b); del b6[(3, 6)]
case("C05c", "rule_hosoku2004 3.⑥", "(constructed)", "L-4, H-3.6", "same igui capture with the Black lion unprotected: lishogi still allows (destination test), JCSA allows (no foot, no sakishishi)",
     b6, "W", (10, 2), usi((5, 8), (5, 8), mid=(4, 7)), "legal", "legal", "counter-strike")

# --- promotion rows ---
b = dict(KINGS); b.update({(2, 11): ("B", "L")})
case("C06", "rule2007 四.4 (vs lishogi: pawn and lance)", "(constructed)", "P-4", "DIFFERENCE: an unpromoted Black lance on rank 11 reaches the last rank with promotion: lishogi allows, JCSA: the lance becomes a dead piece (no promotion)",
     b, "B", None, usi((2, 11), (2, 12), promote=True), "legal", "illegal", "promotion", "correspondence-only clause 四.5 would allow it; not in force over the board")
case("C06b", "rule2007 四.4", "(constructed)", "P-4", "the same lance move without promotion (dead piece afterwards) is legal under both",
     b, "B", None, usi((2, 11), (2, 12)), "legal", "legal", "promotion")
b = dict(KINGS); b.update({(3, 11): ("B", "P")})
case("C07", "rule2007 四.3", "(constructed)", "P-3", "pawn's second chance: an unpromoted Black pawn on rank 11 promotes on reaching the last rank under both",
     b, "B", None, usi((3, 11), (3, 12), promote=True), "legal", "legal", "promotion")
b = dict(KINGS); b.update({(4, 11): ("B", "GB")})
case("C08", "rule_hosoku2004 1 (go-between follows the general rule)", "(constructed)", "P-2, H-1", "go-between: no last-rank promotion under either rule set (it may promote only on entering or by capture)",
     b, "B", None, usi((4, 11), (4, 12), promote=True), "illegal", "illegal", "promotion")

# --- rule_hosoku2004 cases 1–4 (lion rules with three lions; same under both) ---
b = dict(KINGS); b.update({J(3, 3): N, J(2, 2): ("W", "G"), J(1, 2): n, J(2, 1): ("W", "G"), J(1, 3): ("B", "G")})
mv = usi(J(3, 3), J(1, 2), mid=J(2, 2))
case("C09", "rule_hosoku2004 2 ケース1", "Rulegazou.files/image002.gif", "H-2.1", "case 1: Black lion takes gold 2二 and lion 1二 (tsukegui)", b, "B", None, mv, "legal", "legal", "engine")
case("C09b", "rule_hosoku2004 2 ケース1", "Rulegazou.files/image002.gif", "H-2.1", "case 1: then White gold 2一 may take the Black lion on 1二 although it has a foot (lion took lion: no sakishishi)",
     apply(b, mv), "W", None, usi(J(2, 1), J(1, 2)), "legal", "legal", "counter-strike")
b = dict(KINGS); b.update({J(1, 1): ("W", "G"), J(2, 2): n, J(1, 2): n, J(3, 3): N})
case("C10", "rule_hosoku2004 2 ケース2", "Rulegazou.files/image004.gif", "H-2.2", "case 2: Black lion takes the adjacent White lion 2二 and then the lion 1二, both protected by the gold 1一 (adjacent lions are unconditional)",
     b, "B", None, usi(J(3, 3), J(1, 2), mid=J(2, 2)), "legal", "legal", "engine")
b = dict(KINGS); b.update({J(5, 1): ("B", "V"), J(1, 1): n, J(3, 2): n, J(4, 3): ("B", "S"), J(5, 4): N, J(1, 4): ("B", "R")})
mv = usi(J(1, 4), J(1, 1))
case("C11", "rule_hosoku2004 2 ケース3", "Rulegazou.files/image006.gif", "H-2.3", "case 3: Black rook 1四 takes the White lion 1一 (sakishishi: Black's lion 5四 has a foot, the vertical mover 5一)",
     b, "B", None, mv, "legal", "legal", "counter-strike", "the diagram draws the 竪 at 5一 in White's colour but the text calls it 先手の竪行; built as Black's")
b11 = apply(b, mv)
mv2 = usi(J(3, 2), J(5, 4), mid=J(4, 3))
case("C11b", "rule_hosoku2004 2 ケース3, 3.④", "Rulegazou.files/image006.gif", "H-2.3, H-3.4", "case 3: despite the ban, White's lion may take silver 4三 and the Black lion 5四 by tsukegui (tsukegui beats sakishishi; lishogi: the ban never applies to lions)",
     b11, "W", J(1, 1), mv2, "legal", "legal", "counter-strike")
case("C11c", "rule_hosoku2004 2 ケース3", "Rulegazou.files/image006.gif", "H-2.3", "case 3: then Black's vertical mover 5一 strikes the lion on 5四",
     apply(b11, mv2), "B", None, usi(J(5, 1), J(5, 4)), "legal", "legal", "counter-strike")
b = dict(KINGS); b.update({J(2, 1): n, J(2, 2): ("W", "GB"), J(3, 3): N})
case("C12", "rule_hosoku2004 2 ケース4", "Rulegazou.files/image008.gif", "H-2.4", "case 4: the White lion's only foot is the go-between 2二; Black lion may not take go-between and lion in one move (pawn / go-between are no kuisoe pieces; the foot still counts)",
     b, "B", None, usi(J(3, 3), J(2, 1), mid=J(2, 2)), "illegal", "illegal", "engine")
b = dict(KINGS); b.update({J(4, 1): ("W", "D"), J(2, 1): n, J(2, 2): ("W", "P"), J(3, 3): N})
case("C13", "rule_hosoku2004 2 (counter-example to the two-step reading)", "Rulegazou.files/image010.gif", "H-2.4", "Black lion may not take pawn 2二 and the lion 2一 (protected by the dragon 4一) although the lion would be adjacent after the first step: one move, not two",
     b, "B", None, usi(J(3, 3), J(2, 1), mid=J(2, 2)), "illegal", "illegal", "engine")

# --- game end ---
b = {J(1, 4): K, J(5, 1): k, J(2, 5): n}          # after ▲1四酔象成 (prince) and ▽2五獅 (took the king)
case("C14", "rule2007 九 (rule.htm 持将棋 example)", "rule/image005.gif", "E-4, E-6", "after ▽2五獅 took the Black king: Black has only the prince, White king + lion adjacent to it: not a bare-king loss under lishogi (lion adjacent), JCSA: play on (the prince recaptures, then jishogi)",
     b, "B", None, None, "playing", "playing", "status")
b14 = apply(b, usi(J(1, 4), J(2, 5)))
case("C14b", "rule2007 二.6 / 九", "rule/image005.gif", "E-6", "after ▲同太子: king vs king: lishogi 'insufficient material' draw; JCSA jishogi (draw by agreement, neither can mate)",
     b14, "W", None, None, "draw", "draw (jishogi)", "status", "same outcome; JCSA's draw needs the players' agreement")
b = {(5, 1): K, (5, 12): k, (0, 12): ("W", "R"), (11, 12): ("W", "B"), (6, 10): ("W", "G")}
case("C15", "rule2007 二.4–5 vs lishogi bare king", "(constructed)", "E-4", "DIFFERENCE: bare Black king against king + three pieces, none adjacent: lishogi ends the game (bare king), JCSA has no such clause (only K + K + one piece is regulated): play continues",
     b, "B", None, None, "bareking", "playing", "status", "numerically negligible: boards with a bare side are ~1e-70 of the candidate set")
b = {(0, 12): K, (1, 12): ("B", "L"), (0, 11): ("B", "P"), (1, 11): ("B", "P"), (11, 1): k, (10, 3): ("W", "G")}
case("C16", "rule2007 (no stalemate clause); accepted chu shogi convention (D11)", "(constructed)", "E-7", "Black to move has no legal move (king a12 boxed in by its own dead lance and blocked pawns): lishogi: stalemate = loss; JCSA: not stated explicitly, the accepted convention is that the stalemated player loses (same)",
     b, "B", None, None, "stalemate", "stalemate", "status", "terminal under any reading; no count changes")

out = ROOT / "out" / "fixtures" / "jcsa"
out.mkdir(parents=True, exist_ok=True)
json.dump(cases, open(out / "cases.json", "w"), indent=1, ensure_ascii=False)
with open(out / "README.md", "w") as f:
    f.write("# JCSA rule tests: positions, moves, verdicts\n\nGenerated by `build.py`. Coordinates: files a–l from Black's left (JCSA file 12 = a), ranks 1–12 from Black's side (JCSA rank 一 = 12). Lowercase = White. `counter_strike` is the lishogi SFEN flag square. Verdicts: expected (from the texts) / checked (engine for lishogi; `src/jcsa` for the counter-strike rows).\n\n")
    for c in cases:
        f.write(f"## {c['id']}{'  — DIFFERENCE' if c['difference'] else ''}\n\n{c['description']}\n\n- source: {c['source']}; image: `{IMG}{c['image']}`; clauses: {c['text_ref']}\n- sfen: `{c['sfen']}`\n- side to move: {c['side_to_move']}; counter-strike: {c['counter_strike']}; move: `{c['move']}`\n- lishogi: **{c['verdict_lishogi']}** (engine: {c['verdict_lishogi_engine']}); JCSA: **{c['verdict_jcsa']}** (layer: {c['verdict_jcsa_layer']})\n")
        if c['note']:
            f.write(f"- note: {c['note']}\n")
        f.write(f"\n```\n{c['ascii']}\n```\n\n")
print(f"{len(cases)} cases; differences: {sum(c['difference'] for c in cases)}")
