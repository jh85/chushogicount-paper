import ChuShogi.FileBranchCoordinates

/-! Complete suffix aggregation computed once and retained for file selection.
Every cache row is constructed by the checked complete DP. -/
namespace ChuShogi.FileSuffixPlan
open ConcreteDP
abbrev Rows := WeightedDP.Table (List Nat)
def reference (fs : List (List Local)) : Rows :=
  HashAggregation.dp (SummaryCode.encode zero) SummaryCode.merge
    (fun u => SummaryCode.encode (CompactSummary.compactFeature u)) fs

def makeIndex (rs : Rows) : Std.HashMap (List Nat) Nat :=
  HashAggregation.accumulate (rs.map fun e => (SummaryCode.encode (SummaryCode.decode e.1),e.2))

theorem makeIndex_lookup (rs : Rows) (s : Summary) : (makeIndex rs)[SummaryCode.encode s]?.getD 0=
    WeightedDP.integral rs (fun k => if SummaryCode.decode k=s then 1 else 0) := by
  rw [← HashAggregation.lookup_toList]
  unfold WeightedDP.lookup
  rw [makeIndex,HashAggregation.accumulate_integral]
  unfold WeightedDP.integral
  rw [List.map_map]
  simp only [Function.comp_def,SummaryCode.encode_injective.eq_iff]

structure Cache (fs : List (List Local)) where
  rows : Rows
  correct : rows=reference fs
  index : Std.HashMap (List Nat) Nat
  index_correct : index=makeIndex rows

inductive Plan : List (List Local) → Type where
  | nil : Plan []
  | cons (xs : List Local) (fs : List (List Local)) (tail : Plan fs) (cache : Cache (xs::fs)) : Plan (xs::fs)

def rows : {fs : List (List Local)} → Plan fs → Rows
  | [],.nil => [(SummaryCode.encode zero,1)]
  | _::_,.cons _ _ _ cache => cache.rows

theorem rows_correct {fs : List (List Local)} (p : Plan fs) : rows p=reference fs := by
  cases p with
  | nil => rfl
  | cons _ _ _ c => exact c.correct

def index : {fs : List (List Local)} → Plan fs → Std.HashMap (List Nat) Nat
  | [],.nil => makeIndex [(SummaryCode.encode zero,1)]
  | _::_,.cons _ _ _ cache => cache.index

theorem index_correct {fs : List (List Local)} (p : Plan fs) : index p=makeIndex (rows p) := by
  cases p with
  | nil => rfl
  | cons _ _ _ c => exact c.index_correct

@[noinline] def prepare : (fs : List (List Local)) → Plan fs
  | [] => .nil
  | xs::fs =>
    let tail := prepare fs
    let out := HashAggregation.convolve SummaryCode.merge (rows tail)
      (HashAggregation.histogram xs (fun u => SummaryCode.encode (CompactSummary.compactFeature u)))
    .cons xs fs tail ⟨out,by dsimp only [out]; rw [rows_correct]; rfl,makeIndex out,rfl⟩

@[noinline] def lookup {fs : List (List Local)} (p : Plan fs) (s : Summary) : Nat :=
  (index p)[SummaryCode.encode s]?.getD 0

theorem lookup_correct {fs : List (List Local)} (p : Plan fs) (s : Summary) : lookup p s=
    WeightedDP.integral (SummaryCode.groupTable fs) (fun t => if t=s then 1 else 0) := by
  rw [lookup,index_correct,makeIndex_lookup,rows_correct]
  exact (SummaryCode.integral_decode (reference fs) (fun t => if t=s then 1 else 0)).symm

@[noinline] def countWith (finish : Summary → Nat) (accSummary : Summary) {fs : List (List Local)} (p : Plan fs) : Nat :=
  WeightedDP.integral (rows p) (fun k => finish (add accSummary (SummaryCode.decode k)))

theorem countWith_correct (r : Bool) (finish : Summary → Nat)
    (hf : ∀ s, finish s=FileBranchCoordinates.terminal r s)
    (accSummary : Summary) {fs : List (List Local)} (p : Plan fs) :
    countWith finish accSummary p=FileBranchCoordinates.count r accSummary fs := by
  rw [countWith,rows_correct]
  simp only [hf]
  exact (SummaryCode.integral_decode (reference fs) (fun t => FileBranchCoordinates.terminal r (add accSummary t))).symm

end ChuShogi.FileSuffixPlan
