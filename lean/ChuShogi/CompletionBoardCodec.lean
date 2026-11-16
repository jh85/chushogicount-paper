import ChuShogi.ResidualSquareCodec
import ChuShogi.ComputedRendering
import ChuShogi.FileBranchCoordinates

/-! Complete computed completion decoder on actual squares. Its interval is
proved to be the independent completion cardinality. Classical Board universes
occur only in theorem statements and proofs, never in decoding or ranking. -/
namespace ChuShogi.CompletionBoardCodec
set_option maxHeartbeats 1200000
open Specification ConcreteDP BoardDecomposition SummaryBridge SummarySufficiency
open CompletionWordCodec ResidualSquareCodec

def size (r : Bool) (u : Board) : Nat :=
  CompletionWordCodec.size r (boardSummary u) (72-(boardSummary u).d0) (72-(boardSummary u).d1)

@[irreducible] def equivalence (r : Bool) (u : Board) (hu : OnlyConfined u) (h1 : I1 u) (h2 : I2 u) (h3 : I3 u) :
    Fin (size r u) ≃ {f : Board // StratumCompletes r u f} :=
  let e := ResidualProfileCounts.completionWordIso r u hu h1 h2 h3
  (CompletionWordCodec.equivalence r (boardSummary u) (GroupCoverage.sized_board u h1) _ _).trans
    ((profileEquivalence r u hu h1).trans (Equiv.mk e.forward e.backward e.left_inverse e.right_inverse))

theorem size_card (r : Bool) (u : Board) (hu : OnlyConfined u) (h1 : I1 u) (h2 : I2 u) (h3 : I3 u) :
    size r u=FiniteBoards.card (StratumCompletes r u) := by
  rw [ResidualProfileCounts.board_card,← Nat.card_congr (equivalence r u hu h1 h2 h3)]
  simp

theorem tuple_properties (us : List Local) (h : ConcreteDP.Valid us) :
    OnlyConfined (ComputedRendering.tuple us) ∧ I1 (ComputedRendering.tuple us) ∧
      I2 (ComputedRendering.tuple us) ∧ I3 (ComputedRendering.tuple us) := by
  rw [ComputedRendering.tuple_eq us h]
  exact StructuralDecomposition.renderAny_valid us h

def tupleSize (r : Bool) (us : List Local) : Nat := size r (ComputedRendering.tuple us)

def forTuple (r : Bool) (us : List Local) (h : ConcreteDP.Valid us) :
    Fin (tupleSize r us) ≃ {f : Board // StratumCompletes r (StructuralDecomposition.renderAny us) f} :=
  let hp := tuple_properties us h
  (equivalence r (ComputedRendering.tuple us) hp.1 hp.2.1 hp.2.2.1 hp.2.2.2).trans
    (Equiv.subtypeEquiv (Equiv.refl Board) (fun f => by rw [ComputedRendering.tuple_eq us h]; rfl))

theorem tupleSize_terminal (r : Bool) (us : List Local) (h : ConcreteDP.Valid us) :
    tupleSize r us=FileBranchCoordinates.terminal r (CompactSummary.compactSummary us) := by
  have hp := tuple_properties us h
  rw [tupleSize,size_card r _ hp.1 hp.2.1 hp.2.2.1 hp.2.2.2,ComputedRendering.tuple_eq us h]
  rw [FileBranchCoordinates.terminal,EvaluatorRefinement.evaluateNat_compact_weight r _ ⟨us,h,rfl⟩]
  exact (CompactSummary.compactWeight_at r us h).symm

def unrank (r : Bool) (u : Board) (hu : OnlyConfined u) (h1 : I1 u) (h2 : I2 u) (h3 : I3 u) :
    Fin (size r u) → {f : Board // StratumCompletes r u f} :=
  (equivalence r u hu h1 h2 h3).toFun
def rank (r : Bool) (u : Board) (hu : OnlyConfined u) (h1 : I1 u) (h2 : I2 u) (h3 : I3 u) :
    {f : Board // StratumCompletes r u f} → Fin (size r u) :=
  (equivalence r u hu h1 h2 h3).invFun

theorem rank_unrank (r : Bool) (u : Board) (hu : OnlyConfined u) (h1 : I1 u) (h2 : I2 u) (h3 : I3 u)
    (i : Fin (size r u)) : rank r u hu h1 h2 h3 (unrank r u hu h1 h2 h3 i)=i :=
  (equivalence r u hu h1 h2 h3).symm_apply_apply i

theorem unrank_rank (r : Bool) (u : Board) (hu : OnlyConfined u) (h1 : I1 u) (h2 : I2 u) (h3 : I3 u)
    (f : {f : Board // StratumCompletes r u f}) : unrank r u hu h1 h2 h3 (rank r u hu h1 h2 h3 f)=f :=
  (equivalence r u hu h1 h2 h3).apply_symm_apply f

end ChuShogi.CompletionBoardCodec
