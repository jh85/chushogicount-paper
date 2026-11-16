import ChuShogi.FileBranchCoordinates

/-! The file coordinates' terminal weights are the actual completion
cardinalities for the selected valid tuple. This is needed branch by branch;
equality of only the root total would not suffice for ranking or sampling. -/
namespace ChuShogi.FileBranchSemantics
open ConcreteDP FileBranchCoordinates

def tuple (r : Bool) : (fs : List (List Local)) → (p : Summary) → Code r fs p → List Local
  | [],_,_ => []
  | xs::fs,p,x => xs[x.1.val]::tuple r fs (add p (CompactSummary.compactFeature xs[x.1.val])) x.2

def finalSummary (r : Bool) : (fs : List (List Local)) → (p : Summary) → Code r fs p → Summary
  | [],p,_ => p
  | xs::fs,p,x => finalSummary r fs (add p (CompactSummary.compactFeature xs[x.1.val])) x.2

def leafIndex (r : Bool) : (fs : List (List Local)) → (p : Summary) → (x : Code r fs p) →
    Fin (terminal r (finalSummary r fs p x))
  | [],_,x => x
  | xs::fs,p,x => leafIndex r fs (add p (CompactSummary.compactFeature xs[x.1.val])) x.2

theorem tuple_mem (r : Bool) (fs : List (List Local)) (p : Summary) (x : Code r fs p) :
    tuple r fs p x ∈ WeightedDP.tuples fs := by
  induction fs generalizing p with
  | nil => simp [tuple,WeightedDP.tuples]
  | cons xs fs ih =>
    exact List.mem_flatMap.mpr ⟨xs[x.1.val],List.getElem_mem x.1.isLt,
      List.mem_map.mpr ⟨tuple r fs _ x.2,ih _ x.2,rfl⟩⟩

theorem final_summary (r : Bool) (fs : List (List Local)) (p : Summary) (x : Code r fs p) :
    finalSummary r fs p x = add p (CompactSummary.compactSummary (tuple r fs p x)) := by
  induction fs generalizing p with
  | nil => exact (add_zero p).symm
  | cons xs fs ih =>
    change finalSummary r fs _ x.2 = _
    rw [ih]
    exact (add_swap p _ _).symm

theorem root_tuple_valid (r : Bool) (x : Code r files zero) : ConcreteDP.Valid (tuple r files zero x) :=
  (StructuralCount.tuple_mem_iff _).mp (tuple_mem r files zero x)

theorem terminal_card (r : Bool) (x : Code r files zero) :
    terminal r (finalSummary r files zero x) =
      FiniteBoards.card (SummarySufficiency.StratumCompletes r
        (StructuralDecomposition.renderAny (tuple r files zero x))) := by
  rw [final_summary,zero_add]
  have hv := root_tuple_valid r x
  have hs : CompactSummary.RealizedCompact (CompactSummary.compactSummary (tuple r files zero x)) :=
    ⟨tuple r files zero x,hv,rfl⟩
  rw [terminal,EvaluatorRefinement.evaluateNat_compact_weight r _ hs]
  exact CompactSummary.compactWeight_at r _ hv

/-- The residual coordinate has the exact actual-completion interval. Its
efficient decoding to a residual word is a separate next obligation. -/
noncomputable def completionIndex (r : Bool) (x : Code r files zero) :
    Fin (FiniteBoards.card (SummarySufficiency.StratumCompletes r
      (StructuralDecomposition.renderAny (tuple r files zero x)))) :=
  Fin.cast (terminal_card r x) (leafIndex r files zero x)

/-- Local no-duplicate enumeration makes tuple and residual index sufficient
to recover every coordinate. Equal summaries alone do not identify a Board. -/
theorem coordinates_injective (r : Bool) (fs : List (List Local))
    (hn : ∀ xs ∈ fs, xs.Nodup) (p : Summary) (x y : Code r fs p)
    (ht : tuple r fs p x = tuple r fs p y)
    (hi : (leafIndex r fs p x).val = (leafIndex r fs p y).val) : x=y := by
  induction fs generalizing p with
  | nil => exact Fin.ext hi
  | cons xs fs ih =>
    rcases x with ⟨i,x⟩
    rcases y with ⟨j,y⟩
    have he := List.cons.inj ht
    have hij : i=j := Fin.ext ((List.Nodup.getElem_inj (hn xs (by simp))).mp he.1)
    subst j
    have htail : x=y := ih (fun ys hy => hn ys (by simp [hy])) _ x y he.2 hi
    subst y
    rfl

theorem root_coordinates_injective (r : Bool) (x y : Code r files zero)
    (ht : tuple r files zero x = tuple r files zero y)
    (hi : (leafIndex r files zero x).val = (leafIndex r files zero y).val) : x=y :=
  coordinates_injective r files files_nodup zero x y ht hi

end ChuShogi.FileBranchSemantics
