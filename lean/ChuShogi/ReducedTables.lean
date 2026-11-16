import ChuShogi.ReducedGeometry
import ChuShogi.RationalTable

/-! Complete reduced aggregation on (joint,d0,d1,nonpawn-degree). Special type
capacities are integrated once per pair; the final scale is sixteen times four.
-/
namespace ChuShogi.ReducedTables
open Specification Promotion ConcreteDP GroupedFiles ReducedGeometry

def reduce (poly : Summary → WeightedDP.Table Nat) (raw : WeightedDP.Table Summary) : WeightedDP.Table (List Nat) :=
  (HashAggregation.accumulate (raw.flatMap fun e => (poly e.1).map fun p => (key e.1 p.1,e.2*p.2))).toList

theorem map_poly (s : Summary) (w : Nat) (poly : WeightedDP.Table Nat) (f : List Nat → ℚ) :
    RationalTable.integral (poly.map fun p => (key s p.1,w*p.2)) f =
      (w : ℚ)*RationalTable.integral poly (fun k => f (key s k)) := by
  unfold RationalTable.integral
  rw [List.map_map,EGFConvolution.mul_list_sum]
  simp only [Function.comp_def,Nat.cast_mul,mul_assoc]

theorem reduce_integral (poly : Summary → WeightedDP.Table Nat) (raw : WeightedDP.Table Summary)
    (f : List Nat → ℚ) : RationalTable.integral (reduce poly raw) f =
      RationalTable.integral raw (fun s => RationalTable.integral (poly s) (fun k => f (key s k))) := by
  rw [reduce,RationalTable.hash_accumulate,RationalTable.integral_flatMap]
  simp_rw [map_poly]
  rfl

def plain : WeightedDP.Table (List Nat) :=
  (SummaryCode.groupTable plainFiles).map fun e => (key e.1 0,e.2)
def goBetween : WeightedDP.Table (List Nat) := reduce ScaledPolynomials.goBetween (SummaryCode.groupTable goBetweenFiles)
def lance : WeightedDP.Table (List Nat) := reduce ScaledPolynomials.lance (SummaryCode.groupTable lanceFiles)
def table : WeightedDP.Table (List Nat) :=
  HashAggregation.convolve merge (HashAggregation.convolve merge plain goBetween) lance

theorem table_integral (f : List Nat → ℚ) : RationalTable.integral table f =
    RationalTable.integral plainTable (fun p => RationalTable.integral goBetweenTable (fun g =>
      RationalTable.integral lanceTable (fun l =>
        RationalTable.integral (ScaledPolynomials.goBetween g) (fun kg =>
          RationalTable.integral (ScaledPolynomials.lance l) (fun kl => f (key (SpecialPolynomials.joined p g l) (kg+kl))))))) := by
  unfold table
  simp only [RationalTable.hash_convolve (S := List Nat),RationalTable.integral_convolve (S := List Nat)]
  simp only [plain,goBetween,lance]
  rw [RationalTable.integral_map_key (SummaryCode.groupTable plainFiles) (fun s => key s 0)]
  simp_rw [reduce_integral,RationalTable.hash_group]
  simp_rw [merge_key,Nat.zero_add]
  apply congrArg (RationalTable.integral plainTable)
  funext p
  apply congrArg (RationalTable.integral goBetweenTable)
  funext g
  exact RationalTable.integral_exchange (ScaledPolynomials.goBetween g) lanceTable
    (fun kg l => RationalTable.integral (ScaledPolynomials.lance l)
      (fun kl => f (key (SpecialPolynomials.joined p g l) (kg+kl))))

theorem compact_evaluate (r : Bool) : RationalTable.integral CompactSummary.compactTable
    (CompletionCoefficients.evaluate r) = (FiniteBoards.card (StructuralDecomposition.Stratum r) : ℚ) := by
  have he : RationalTable.integral CompactSummary.compactTable (CompletionCoefficients.evaluate r) =
      RationalTable.integral CompactSummary.compactTable (fun s => (EvaluatorRefinement.evaluateNat r s : ℚ)) := by
    rw [CompactSummary.compactTable,RationalTable.dp_integral,RationalTable.dp_integral]
    apply congrArg List.sum
    apply List.map_congr_left
    intro us hu
    have hs : CompactSummary.RealizedCompact (CompactSummary.compactSummary us) :=
      ⟨us,(StructuralCount.tuple_mem_iff us).mp hu,rfl⟩
    change CompletionCoefficients.evaluate r (CompactSummary.compactSummary us) =
      (EvaluatorRefinement.evaluateNat r (CompactSummary.compactSummary us) : ℚ)
    rw [EvaluatorRefinement.evaluate_compact_weight r _ hs,EvaluatorRefinement.evaluateNat_compact_weight r _ hs]
  rw [he,RationalTable.integral_cast]
  exact congrArg (fun n : Nat => (n : ℚ)) (ExecutableCounter.count_compact r)

/-- Complete scaled total: all file states, all special multiplicities and all
completion contributions are present. No externally supplied coverage premise. -/
theorem scaled_total (r : Bool) : RationalTable.integral table (finish r) =
    64*(FiniteBoards.card (StructuralDecomposition.Stratum r) : ℚ) := by
  rw [table_integral]
  have he : RationalTable.integral plainTable (fun p => RationalTable.integral goBetweenTable (fun g =>
      RationalTable.integral lanceTable (fun l =>
        RationalTable.integral (ScaledPolynomials.goBetween g) (fun kg =>
          RationalTable.integral (ScaledPolynomials.lance l) (fun kl => finish r (key (SpecialPolynomials.joined p g l) (kg+kl))))))) =
      RationalTable.integral plainTable (fun p => RationalTable.integral goBetweenTable (fun g =>
        RationalTable.integral lanceTable (fun l => 64*CompletionCoefficients.evaluate r (SpecialPolynomials.joined p g l)))) := by
    apply RationalTable.integral_congr
    intro pe hp
    apply RationalTable.integral_congr
    intro ge hg
    apply RationalTable.integral_congr
    intro le hl
    exact actual_scaled r pe ge le hp hg hl
  rw [he]
  simp_rw [RationalTable.integral_mul (w := 64)]
  have ht : RationalTable.integral GroupedFiles.groupedTable (CompletionCoefficients.evaluate r) =
      RationalTable.integral plainTable (fun p => RationalTable.integral goBetweenTable (fun g =>
        RationalTable.integral lanceTable (fun l => CompletionCoefficients.evaluate r (SpecialPolynomials.joined p g l)))) := by
    simp only [GroupedFiles.groupedTable,RationalTable.integral_convolve]
    rfl
  rw [← ht,RationalTable.grouped,compact_evaluate]

def count (r : Bool) : ℚ := RationalTable.integral table (finish r)/64

theorem count_correct (r : Bool) : count r = (FiniteBoards.card (StructuralDecomposition.Stratum r) : ℚ) := by
  rw [count,scaled_total]
  ring

end ChuShogi.ReducedTables
