#include "eng.h"

#include "../../../out/engine/src/sfen.h"

namespace cp {

static const char* INITIAL =
    "lfcsgekgscfl/a1b1txot1b1a/mvrhdqndhrvm/pppppppppppp/3i4i3/12/12/"
    "3I4I3/PPPPPPPPPPPP/MVRHDNQDHRVM/A1B1TOXT1B1A/LFCSGKEGSCFL b - 1";

int to_esq(int s) { return (12 - SR(s)) * 12 + (11 - SX(s)); }
int from_esq(int e) { return SQ(11 - chu::sqX(e), 12 - chu::sqY(e)); }

static int from_erole(chu::Role r) {
  switch (r) {
    case chu::Pawn: return P; case chu::Lance: return L; case chu::GoBetween: return GB;
    case chu::Chariot: return RC; case chu::SideMover: return M; case chu::VerticalMover: return V;
    case chu::Copper: return C; case chu::Silver: return S; case chu::Leopard: return F;
    case chu::Tiger: return T; case chu::Gold: return G; case chu::Elephant: return E;
    case chu::Bishop: return B; case chu::Rook: return R; case chu::Horse: return H;
    case chu::Dragon: return D; case chu::Kirin: return O; case chu::Phoenix: return X;
    case chu::King: return K; case chu::Lion: return N; case chu::Queen: return Q;
    case chu::Tokin: return pP; case chu::WhiteHorse: return pL; case chu::ElephantP: return pGB;
    case chu::Whale: return pRC; case chu::Boar: return pM; case chu::Ox: return pV;
    case chu::SideMoverP: return pC; case chu::VerticalMoverP: return pS; case chu::BishopP: return pF;
    case chu::Stag: return pT; case chu::RookP: return pG; case chu::HorseP: return pB;
    case chu::DragonP: return pR; case chu::Falcon: return pH; case chu::Eagle: return pD;
    case chu::LionP: return N; case chu::QueenP: return Q; case chu::Prince: return K;
    default: return -1;
  }
}

static chu::Role to_erole(int r) {
  switch (r) {
    case P: return chu::Pawn; case L: return chu::Lance; case GB: return chu::GoBetween;
    case RC: return chu::Chariot; case M: return chu::SideMover; case V: return chu::VerticalMover;
    case C: return chu::Copper; case S: return chu::Silver; case F: return chu::Leopard;
    case T: return chu::Tiger; case G: return chu::Gold; case E: return chu::Elephant;
    case B: return chu::Bishop; case R: return chu::Rook; case H: return chu::Horse;
    case D: return chu::Dragon; case O: return chu::Kirin; case X: return chu::Phoenix;
    case K: return chu::King; case N: return chu::Lion; case Q: return chu::Queen;
    case pP: return chu::Tokin; case pL: return chu::WhiteHorse; case pGB: return chu::ElephantP;
    case pRC: return chu::Whale; case pM: return chu::Boar; case pV: return chu::Ox;
    case pC: return chu::SideMoverP; case pS: return chu::VerticalMoverP; case pF: return chu::BishopP;
    case pT: return chu::Stag; case pG: return chu::RookP; case pB: return chu::HorseP;
    case pR: return chu::DragonP; case pH: return chu::Falcon; case pD: return chu::Eagle;
    default: return chu::RoleCount;
  }
}

void Eng::set_initial() {
  chu::parseSfen(INITIAL, pos_);
  valid_ = false;
}

void Eng::set_board(const Board& b, int turn, int flag) {
  chu::Position p;
  p.board.fill(0);
  for (int s = 0; s < 144; ++s)
    if (b[s]) p.board[to_esq(s)] = chu::makePiece(to_erole(role_of(b[s])), colour_of(b[s]) == 0 ? chu::Sente : chu::Gote);
  p.sideToMove = turn == 0 ? chu::Sente : chu::Gote;
  p.lastLionCapture = flag < 0 ? chu::kNoSquare : (int16_t)to_esq(flag);
  p.moveNumber = 1;
  p.rules = chu::RuleSet::Lishogi;
  pos_ = p;
  valid_ = false;
}

const std::vector<chu::Move>& Eng::legal() {
  if (!valid_) {
    legal_ = chu::generateLegal(pos_);
    valid_ = true;
  }
  return legal_;
}

static chu::Move to_emove(const PMove& m) {
  chu::Move e;
  e.from = (int16_t)to_esq(m.from);
  e.mid = m.mid >= 0 ? (int16_t)to_esq(m.mid) : (int16_t)chu::kNoSquare;
  e.to = (int16_t)to_esq(m.to);
  e.promote = m.promote;
  return e;
}

bool Eng::is_legal(const PMove& m) {
  chu::Move e = to_emove(m);
  for (const auto& l : legal())
    if (l.from == e.from && l.mid == e.mid && l.to == e.to && l.promote == e.promote) return true;
  return false;
}

void Eng::move(const PMove& m) {
  if (!is_legal(m)) throw PyExc{"AssertionError", "('" + usi(m) + "', 'illegal')"};
  pos_.apply(to_emove(m));
  valid_ = false;
}

bool Eng::playing() { return chu::evaluateStatus(pos_).end == chu::GameEnd::Playing; }

Piece from_epiece(uint8_t p) {
  return mk(chu::colorOf(p) == chu::Sente ? 0 : 1, from_erole(chu::roleOf(p)));
}

void Eng::state(Board& b, int& turn, int& flag) const {
  b.fill(0);
  for (int e = 0; e < 144; ++e) {
    uint8_t p = pos_.board[e];
    if (!p) continue;
    b[from_esq(e)] = mk(chu::colorOf(p) == chu::Sente ? 0 : 1, from_erole(chu::roleOf(p)));
  }
  turn = pos_.sideToMove == chu::Sente ? 0 : 1;
  flag = pos_.lastLionCapture == chu::kNoSquare ? -1 : from_esq(pos_.lastLionCapture);
}

}  // namespace cp
