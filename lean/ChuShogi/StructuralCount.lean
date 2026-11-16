import ChuShogi.FiniteBoards

/-! The structural counting theorem for both independent Candidate strata.
Weights are actual finite completion cardinalities, chosen by summary using the
proved completion bijections. They are not yet the executable EGF formula. -/
namespace ChuShogi.StructuralCount
open Specification Promotion ConcreteDP BoardDecomposition SummaryBridge Rendering
open Completion SummarySufficiency StructuralDecomposition FiniteBoards

noncomputable def completionBoards (r : Bool) (u : Board) : List Board := by
  classical
  exact allBoards.filter fun f => decide (StratumCompletes r u f)

theorem completionBoards_iff (r : Bool) (u f : Board) :
    f ∈ completionBoards r u ↔ StratumCompletes r u f := by
  classical
  simp [completionBoards,universe_complete]

theorem completionBoards_nodup (r : Bool) (u : Board) : (completionBoards r u).Nodup := by
  classical
  exact universe_nodup.filter _

theorem completionBoards_length (r : Bool) (u : Board) :
    (completionBoards r u).length = card (StratumCompletes r u) := by
  rw [card,subtypeEnum_length]
  rfl

noncomputable def partList (r : Bool) : List Parts :=
  (WeightedDP.tuples files).flatMap fun us => (completionBoards r (renderAny us)).map (us, ·)

theorem tuple_mem_iff (us : List Local) : us ∈ WeightedDP.tuples files ↔ ConcreteDP.Valid us :=
  WeightedDP.tuples_iff admissible files (enumerates indices) us

theorem partList_iff (r : Bool) (p : Parts) : p ∈ partList r ↔ ValidParts r p := by
  rcases p with ⟨us,f⟩
  simp only [partList,List.mem_flatMap,List.mem_map,Prod.mk.injEq]
  constructor
  · rintro ⟨vs,hv,g,hg,rfl,rfl⟩
    exact ⟨(tuple_mem_iff _).mp hv,(completionBoards_iff _ _ _).mp hg⟩
  · rintro ⟨hu,hf⟩
    exact ⟨us,(tuple_mem_iff _).mpr hu,f,(completionBoards_iff _ _ _).mpr hf,rfl,rfl⟩

theorem partList_nodup (r : Bool) : (partList r).Nodup := by
  simp only [partList,List.nodup_iff_pairwise_ne,List.pairwise_flatMap,List.pairwise_map]
  constructor
  · intro us _
    apply List.Pairwise.imp _ (completionBoards_nodup r (renderAny us))
    intro f g hfg he
    exact hfg (Prod.mk.inj he).2
  · apply List.Pairwise.imp _ (WeightedDP.tuples_nodup files files_nodup)
    intro us vs huv p hp q hq he
    obtain ⟨f,_,rfl⟩ := List.mem_map.mp hp
    obtain ⟨g,_,rfl⟩ := List.mem_map.mp hq
    exact huv (Prod.mk.inj he).1

/-- Sum over all independent tuple fibres, with actual completion cardinalities. -/
theorem sum_completions (r : Bool) :
    card (Stratum r) = ((WeightedDP.tuples files).map fun us => card (StratumCompletes r (renderAny us))).sum := by
  have hc : ∀ p, ValidParts r p → p ∈ partList r := fun p hp => (partList_iff r p).mpr hp
  have hi := iso_lengths (subtypeEnum (partList r) (ValidParts r))
    (subtypeEnum allBoards (Stratum r))
    (subtypeEnum_nodup _ (partList_nodup r) _) (subtypeEnum_nodup _ universe_nodup _)
    (subtypeEnum_complete_of _ _ hc) (subtypeEnum_complete _ universe_complete _)
    (decompositionIso r)
  rw [subtypeEnum_length_of _ _ (fun p hp => (partList_iff r p).mp hp)] at hi
  change (partList r).length = card (Stratum r) at hi
  rw [← hi,partList,List.length_flatMap]
  simp only [List.length_map,completionBoards_length]

/-- Reachability here means a summary has a valid tuple, not full-game reachability. -/
def Realized (s : Summary) : Prop := ∃ us, ConcreteDP.Valid us ∧ summary us = s

noncomputable def weight (r : Bool) (s : Summary) : Nat := by
  classical
  exact if h : Realized s then card (StratumCompletes r (renderAny (Classical.choose h))) else 0

theorem summary_renderAny (us : List Local) (h : ConcreteDP.Valid us) :
    boardSummary (renderAny us) = summary us := by
  unfold boardSummary
  rw [boardTuple_renderAny us h]

/-- True completion cardinality factors through the actual 13-field summary. -/
theorem weight_at_tuple (r : Bool) (us : List Local) (h : ConcreteDP.Valid us) :
    weight r (summary us) = card (StratumCompletes r (renderAny us)) := by
  have hs : Realized (summary us) := ⟨us,h,rfl⟩
  simp only [weight,dite_eq_left hs]
  have hp := Classical.choose_spec hs
  have hv := renderAny_valid (Classical.choose hs) hp.1
  have hu := renderAny_valid us h
  apply card_iso
  apply stratumIso r _ _ hv.1 hu.1 hv.2.1 hv.2.2.1 hv.2.2.2 hu.2.1 hu.2.2.1 hu.2.2.2
  rw [summary_renderAny _ hp.1,summary_renderAny us h]
  exact hp.2

/-- Abstract DP total with mathematically defined completion cardinalities. -/
noncomputable def structuralCount (r : Bool) : Nat := WeightedDP.integral table (weight r)

/-- Complete structural counting theorem: all enumeration, decomposition, summary
and completion-cardinality hypotheses have been discharged. -/
theorem structural_count (r : Bool) : structuralCount r = card (Stratum r) := by
  rw [structuralCount,concrete_dp_integral,sum_completions]
  apply congrArg List.sum
  apply List.map_congr_left
  intro us hu
  exact weight_at_tuple r us ((tuple_mem_iff us).mp hu)

theorem count_C_r : structuralCount true = card C_r := structural_count true

theorem count_C_nr : structuralCount false = card C_nr := structural_count false

end ChuShogi.StructuralCount
