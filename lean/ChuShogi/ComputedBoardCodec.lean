import ChuShogi.FileTupleCodec
import ChuShogi.FiniteSigmaCodec
import ChuShogi.CompletionBoardCodec
import ChuShogi.ComputedDecomposition
import ChuShogi.CachedArithmetic

/-! Complete computed Board rank/unrank, with all application-specific branch
and terminal-coverage obligations discharged. The file selector here recomputes
compressed suffix counts; caching refinements can reuse the same inverse laws.
-/
namespace ChuShogi.ComputedBoardCodec
set_option maxHeartbeats 1200000
open Specification ConcreteDP StructuralDecomposition SummarySufficiency FileBranchCoordinates
attribute [local irreducible] ConcreteDP.files FileBranchCoordinates.equivalence
  FileBranchCoordinates.count CachedArithmetic.count

abbrev TupleCoordinates (r : Bool) := Σ us : {us : List Local // ConcreteDP.Valid us}, Fin (CompletionBoardCodec.tupleSize r us.val)

@[irreducible] def rootTupleEquivalence (r : Bool) : FileTupleCodec.Coordinates r files zero ≃ TupleCoordinates r :=
  FiniteSigmaCodec.equivalence (fun us => us ∈ WeightedDP.tuples files) ConcreteDP.Valid
    StructuralCount.tuple_mem_iff
    (fun us => terminal r (add zero (CompactSummary.compactSummary us)))
    (CompletionBoardCodec.tupleSize r)
    (fun us hm => by
      rw [zero_add,CompletionBoardCodec.tupleSize_terminal r us ((StructuralCount.tuple_mem_iff us).mp hm)])

def flatten (r : Bool) :
    (Σ us : {us : List Local // ConcreteDP.Valid us}, {f : Board // StratumCompletes r (renderAny us.val) f}) ≃
      {p : Parts // ValidParts r p} where
  toFun p := ⟨(p.1.val,p.2.val),p.1.property,p.2.property⟩
  invFun p := ⟨⟨p.val.1,p.property.1⟩,⟨p.val.2,p.property.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[irreducible] def partsEquivalence (r : Bool) : FileBranchCoordinates.Code r files zero ≃ {p : Parts // ValidParts r p} := by
  let a : FileBranchCoordinates.Code r files zero ≃ FileTupleCodec.Coordinates r files zero :=
    FileTupleCodec.equivalence r files files_nodup zero
  let b : FileTupleCodec.Coordinates r files zero ≃ TupleCoordinates r := rootTupleEquivalence r
  let c : TupleCoordinates r ≃
      (Σ us : {us : List Local // ConcreteDP.Valid us}, {f : Board // StratumCompletes r (renderAny us.val) f}) :=
    Equiv.sigmaCongrRight (fun us : {us : List Local // ConcreteDP.Valid us} =>
      CompletionBoardCodec.forTuple r us.val us.property)
  exact a.trans (b.trans (c.trans (flatten r)))

@[irreducible] def equivalence (r : Bool) : Fin (FileBranchCoordinates.count r zero files) ≃ {b : Board // Stratum r b} :=
  (FileBranchCoordinates.equivalence r files zero).trans
    ((partsEquivalence r).trans (ComputedDecomposition.equivalence r))

theorem counter_size (r : Bool) : FileBranchCoordinates.count r zero files=CachedArithmetic.count r :=
  (FileBranchCoordinates.root_count r).trans (CachedArithmetic.count_correct r).symm

@[irreducible] def counterEquivalence (r : Bool) : Fin (CachedArithmetic.count r) ≃ {b : Board // Stratum r b} :=
  (finCongr (counter_size r).symm).trans (equivalence r)

def unrank (r : Bool) : Fin (CachedArithmetic.count r) → {b : Board // Stratum r b} := (counterEquivalence r).toFun
def rank (r : Bool) : {b : Board // Stratum r b} → Fin (CachedArithmetic.count r) := (counterEquivalence r).invFun

theorem rank_unrank (r : Bool) (i : Fin (CachedArithmetic.count r)) : rank r (unrank r i)=i :=
  (counterEquivalence r).symm_apply_apply i

theorem unrank_rank (r : Bool) (b : {b : Board // Stratum r b}) : unrank r (rank r b)=b :=
  (counterEquivalence r).apply_symm_apply b

theorem uniform_input (r : Bool) (p : PMF (Fin (CachedArithmetic.count r)))
    (h : ∀ i, p i=(CachedArithmetic.count r : ENNReal)⁻¹) (b : {b : Board // Stratum r b}) :
    (p.map (unrank r)) b=(CachedArithmetic.count r : ENNReal)⁻¹ :=
  MathSampling.uniform_equiv (counterEquivalence r) p _ h b

end ChuShogi.ComputedBoardCodec
