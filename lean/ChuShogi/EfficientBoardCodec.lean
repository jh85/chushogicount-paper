import ChuShogi.SummaryFirstCodec
import ChuShogi.CompletionCache
import ChuShogi.ComputedBoardCodec

/-! Reusable suffix/weight preparation and summary-first Board indexing. All
state coverage is inherited from the complete checked DP and conditioned
selector; no supplied partial list is assumed sufficient. -/
namespace ChuShogi.EfficientBoardCodec
open Specification ConcreteDP FileSuffixPlan StructuralDecomposition
attribute [local irreducible] ConcreteDP.files CachedArithmetic.count

structure Prepared (r : Bool) where
  plan : Plan files
  completion : CompletionCache.Prepared r

@[noinline] def prepare (r : Bool) : Prepared r :=
  let p := FileSuffixPlan.prepare files
  ⟨p,CompletionCache.prepare r (rows p)⟩

def size (p : Prepared r) : Nat := SummaryFirstCodec.size (CompletionCache.finish p.completion) p.plan

theorem size_counter (p : Prepared r) : size p=CachedArithmetic.count r := by
  rw [size,SummaryFirstCodec.size_integral,rows_correct]
  have hf : CompletionCache.finish p.completion=FileBranchCoordinates.terminal r :=
    funext (CompletionCache.finish_correct p.completion)
  rw [hf]
  have he := SummaryCode.integral_decode (reference files) (fun s => FileBranchCoordinates.terminal r s)
  change WeightedDP.integral (reference files) (fun k => FileBranchCoordinates.terminal r (SummaryCode.decode k))=_
  rw [← he]
  have hc := FileBranchCoordinates.root_count r
  unfold FileBranchCoordinates.count at hc
  simp only [FileBranchCoordinates.zero_add] at hc
  exact hc.trans (CachedArithmetic.count_correct r).symm

@[irreducible] def tupleEquivalence (p : Prepared r) :
    (Σ us : SummaryFirstCodec.Tuples files, Fin (CompletionCache.finish p.completion (CompactSummary.compactSummary us.val))) ≃
      ComputedBoardCodec.TupleCoordinates r :=
  FiniteSigmaCodec.equivalence (fun us => us∈WeightedDP.tuples files) ConcreteDP.Valid StructuralCount.tuple_mem_iff
    (fun us => CompletionCache.finish p.completion (CompactSummary.compactSummary us))
    (CompletionBoardCodec.tupleSize r)
    (fun us hm => by
      rw [CompletionCache.finish_correct,CompletionBoardCodec.tupleSize_terminal r us ((StructuralCount.tuple_mem_iff us).mp hm)]
      rfl)

@[irreducible] def equivalence (p : Prepared r) : Fin (size p) ≃ {b : Board // Stratum r b} := by
  let a := SummaryFirstCodec.equivalence (CompletionCache.finish p.completion) p.plan files_nodup
  let b : ComputedBoardCodec.TupleCoordinates r ≃
      (Σ us : {us : List Local // ConcreteDP.Valid us}, {f : Board // SummarySufficiency.StratumCompletes r (renderAny us.val) f}) :=
    Equiv.sigmaCongrRight (fun us : {us : List Local // ConcreteDP.Valid us} =>
      CompletionBoardCodec.forTuple r us.val us.property)
  exact a.trans ((tupleEquivalence p).trans (b.trans
    ((ComputedBoardCodec.flatten r).trans (ComputedDecomposition.equivalence r))))

@[irreducible] def counterEquivalence (p : Prepared r) : Fin (CachedArithmetic.count r) ≃ {b : Board // Stratum r b} :=
  (finCongr (size_counter p).symm).trans (equivalence p)

/-- Store the constructed closures so repeated calls retain suffixes and
branch lists rather than constructing another prepared counting environment. -/
structure Runtime (r : Bool) where
  codec : Fin (CachedArithmetic.count r) ≃ {b : Board // Stratum r b}

@[noinline] def runtime (p : Prepared r) : Runtime r := ⟨counterEquivalence p⟩
def unrank (p : Runtime r) := p.codec.toFun
def rank (p : Runtime r) := p.codec.invFun

theorem rank_unrank (p : Runtime r) (i : Fin (CachedArithmetic.count r)) : rank p (unrank p i)=i := p.codec.symm_apply_apply i
theorem unrank_rank (p : Runtime r) (b : {b : Board // Stratum r b}) : unrank p (rank p b)=b := p.codec.apply_symm_apply b

theorem uniform_input (p : Runtime r) (d : PMF (Fin (CachedArithmetic.count r)))
    (h : ∀ i, d i=(CachedArithmetic.count r : ENNReal)⁻¹) (b : {b : Board // Stratum r b}) :
    (d.map (unrank p)) b=(CachedArithmetic.count r : ENNReal)⁻¹ :=
  MathSampling.uniform_equiv p.codec d _ h b

/-- Closed application: every suffix and cache hypothesis is supplied by the
actual constructors, rather than left to a caller. Retain the constructed
runtime once when executing repeated operations. -/
theorem prepared_rank_unrank (r : Bool) (i : Fin (CachedArithmetic.count r)) :
    rank (runtime (prepare r)) (unrank (runtime (prepare r)) i)=i :=
  rank_unrank (runtime (prepare r)) i

theorem prepared_unrank_rank (r : Bool) (b : {b : Board // Stratum r b}) :
    unrank (runtime (prepare r)) (rank (runtime (prepare r)) b)=b :=
  unrank_rank (runtime (prepare r)) b

end ChuShogi.EfficientBoardCodec
