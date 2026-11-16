import ChuShogi.StructuralCount

/-! Default-source compaction: pawn statistics are optional and do not determine
completion counts. The compact DP erases them before aggregation. -/
namespace ChuShogi.CompactSummary
open Specification Promotion ConcreteDP BoardDecomposition SummaryBridge OccupancyBridge
open ResidualSquares Completion SummarySufficiency StructuralDecomposition StructuralCount FiniteBoards

def erase (s : Summary) : Summary := {s with uPB := 0,uPW := 0}

theorem conditions_erase (s : Summary) (f : Board) : FreeConditions (erase s) f ↔ FreeConditions s f := by
  have hc (c : Colour) (k : Kind) : cap (erase s) c k = cap s c k := by cases c <;> cases k <;> rfl
  simp only [FreeConditions,Bounds,hc]
  rfl

def geometry (u v : Board) (hu : OnlyConfined u) (hv : OnlyConfined v) (hu1 : I1 u) (hv1 : I1 v)
    (he : erase (boardSummary u) = erase (boardSummary v)) : ResidualSquares.Relabelling u v := by
  apply of_occupied_counts
  intro a
  by_cases ha : a < 2
  · have hh := congrArg (fun s => occupiedField s a) he
    have hf (s : Summary) : occupiedField (erase s) a = occupiedField s a := by
      unfold occupiedField erase
      rfl
    rw [hf,hf,boardSummary_occupied u hu1 hu a ha,boardSummary_occupied v hv1 hv a ha] at hh
    exact hh
  · rw [occupied_high u a (by omega),occupied_high v a (by omega)]

theorem move_completion (u v f : Board) (hu : OnlyConfined u) (hv : OnlyConfined v)
    (hu1 : I1 u) (hu2 : I2 u) (hu3 : I3 u) (hv1 : I1 v) (hv2 : I2 v) (hv3 : I3 v)
    (he : erase (boardSummary u) = erase (boardSummary v)) (e : ResidualSquares.Relabelling u v)
    (h : Completes u f) : Completes v (Placement.transport e.toRelabelling f) := by
  obtain ⟨hf,hd,hc⟩ := (completes_iff u f hu hu1 hu2 hu3).mp h
  apply (completes_iff v _ hv hv1 hv2 hv3).mpr
  refine ⟨transport_onlyFree u v f e hf,transport_disjoint u v f e hd,?_⟩
  rw [transport_conditions]
  apply (conditions_erase _ _).mp
  rw [← he]
  exact (conditions_erase _ _).mpr hc

theorem move_stratum (r : Bool) (u v f : Board) (hu : OnlyConfined u) (hv : OnlyConfined v)
    (hu1 : I1 u) (hu2 : I2 u) (hu3 : I3 u) (hv1 : I1 v) (hv2 : I2 v) (hv3 : I3 v)
    (he : erase (boardSummary u) = erase (boardSummary v)) (e : ResidualSquares.Relabelling u v)
    (h : StratumCompletes r u f) : StratumCompletes r v (Placement.transport e.toRelabelling f) := by
  obtain ⟨hc,hr⟩ := (stratum_iff r u f hu).mp h
  apply (stratum_iff r v _ hv).mpr
  exact ⟨move_completion u v f hu hv hu1 hu2 hu3 hv1 hv2 hv3 he e hc,
    (transport_royalMode r u v f e).mpr hr⟩

/-- Concrete completion sufficiency also holds after optional pawn statistics
are erased, as in Python count(..., stats=False). -/
def compactIso (r : Bool) (u v : Board) (hu : OnlyConfined u) (hv : OnlyConfined v)
    (hu1 : I1 u) (hu2 : I2 u) (hu3 : I3 u) (hv1 : I1 v) (hv2 : I2 v) (hv3 : I3 v)
    (he : erase (boardSummary u) = erase (boardSummary v)) :
    FiniteRelabelling.Iso {f // StratumCompletes r u f} {f // StratumCompletes r v f} := by
  let e := geometry u v hu hv hu1 hv1 he
  refine ⟨(fun f => ⟨Placement.transport e.toRelabelling f.val,
      move_stratum r u v f.val hu hv hu1 hu2 hu3 hv1 hv2 hv3 he e f.property⟩),
    (fun f => ⟨Placement.transport (inverse u v e).toRelabelling f.val,
      move_stratum r v u f.val hv hu hv1 hv2 hv3 hu1 hu2 hu3 he.symm (inverse u v e) f.property⟩),?_,?_⟩
  · intro f; apply Subtype.ext; exact Placement.transport_inverse e.toRelabelling f.val
  · intro f; apply Subtype.ext; exact Placement.inverse_transport e.toRelabelling f.val

def compactFeature (u : Local) : Summary := erase (feature u)
def compactSummary (us : List Local) : Summary := WeightedDP.summary zero add compactFeature us

theorem summary_compact (us : List Local) : compactSummary us = erase (summary us) := by
  induction us with
  | nil => rfl
  | cons u us ih =>
    change add (compactSummary us) (erase (feature u)) = erase (add (summary us) (feature u))
    rw [ih]
    rfl

def compactTable : WeightedDP.Table Summary := WeightedDP.dp zero add compactFeature files

def RealizedCompact (s : Summary) : Prop := ∃ us, ConcreteDP.Valid us ∧ compactSummary us = s

noncomputable def compactWeight (r : Bool) (s : Summary) : Nat := by
  classical
  exact if h : RealizedCompact s then card (StratumCompletes r (renderAny (Classical.choose h))) else 0

theorem compactWeight_at (r : Bool) (us : List Local) (h : ConcreteDP.Valid us) :
    compactWeight r (compactSummary us) = card (StratumCompletes r (renderAny us)) := by
  have hs : RealizedCompact (compactSummary us) := ⟨us,h,rfl⟩
  simp only [compactWeight,dite_eq_left hs]
  have hp := Classical.choose_spec hs
  have hv := renderAny_valid (Classical.choose hs) hp.1
  have hu := renderAny_valid us h
  apply card_iso
  apply compactIso r _ _ hv.1 hu.1 hv.2.1 hv.2.2.1 hv.2.2.2 hu.2.1 hu.2.2.1 hu.2.2.2
  rw [summary_renderAny _ hp.1,summary_renderAny us h,← summary_compact,← summary_compact]
  exact hp.2

noncomputable def compactCount (r : Bool) : Nat := WeightedDP.integral compactTable (compactWeight r)

/-- Abstract structural total for the actual source's default summary compaction. -/
theorem compact_count (r : Bool) : compactCount r = card (Stratum r) := by
  rw [compactCount,compactTable,WeightedDP.dp_integral,sum_completions]
  apply congrArg List.sum
  apply List.map_congr_left
  intro us hu
  exact compactWeight_at r us ((tuple_mem_iff us).mp hu)

theorem compact_C_r : compactCount true = card C_r := compact_count true
theorem compact_C_nr : compactCount false = card C_nr := compact_count false

end ChuShogi.CompactSummary
