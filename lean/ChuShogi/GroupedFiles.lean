import ChuShogi.AggregationOrder

/-! Actual three-way file partition used by the efficient calculation. The
capacity conversion must occur after each overlapping special-type pair has
been aggregated; converting individual eligible origins would overcount.
-/
namespace ChuShogi.GroupedFiles
open Specification Promotion ConcreteDP SummaryBridge WeightedDP AggregationOrder

def lanceFiles : List (List Local) := [localConfigs 11,localConfigs 0]
def goBetweenFiles : List (List Local) := [localConfigs 8,localConfigs 3]
def plainFiles : List (List Local) := plainIndices.map localConfigs

def lanceTable : Table Summary := dp zero add CompactSummary.compactFeature lanceFiles
def goBetweenTable : Table Summary := dp zero add CompactSummary.compactFeature goBetweenFiles
def plainTable : Table Summary := dp zero add CompactSummary.compactFeature plainFiles

def groupedTable : Table Summary := convolve add (convolve add plainTable goBetweenTable) lanceTable

theorem add_zero (s : Summary) : add s zero = s := by cases s; simp [add,zero]

theorem reordered_grouped (f : Summary → Nat) : integral reorderedTable f = integral groupedTable f := by
  change integral (dp zero add CompactSummary.compactFeature (lanceFiles++(goBetweenFiles++plainFiles))) f = _
  rw [dp_append zero add CompactSummary.compactFeature add_assoc add_zero]
  rw [integral_convolve,dp_append zero add CompactSummary.compactFeature add_assoc add_zero]
  rw [groupedTable,integral_convolve add (convolve add plainTable goBetweenTable) lanceTable f]
  rfl

/-- No file configurations, states or summary transitions are omitted by this
partition/reordering, for arbitrary completion weights. -/
theorem grouped_integral (f : Summary → Nat) : integral groupedTable f = integral CompactSummary.compactTable f :=
  (reordered_grouped f).symm.trans (reordered_integral f)

theorem localCap_no_slot (u : Local) (c : Colour) (k : Kind) (h : ¬ HasSlot u.1 c k) : localCap u c k = 0 := by
  simp [localCap,bit,h]

theorem plain_cap_zero (u : Local)
    (h : u.1.val ≠ 0 ∧ u.1.val ≠ 11 ∧ u.1.val ≠ 3 ∧ u.1.val ≠ 8)
    (c : Colour) (k : Kind) (hk : k ≠ .pawn) : cap (feature u) c k = 0 := by
  have hn : ¬ HasSlot u.1 c k := by
    cases k <;> simp [HasSlot,h.1,h.2.1,h.2.2.1,h.2.2.2] at hk ⊢
  cases c <;> cases k <;> first | contradiction | exact localCap_no_slot u _ _ hn

theorem lance_goBetween_zero (u : Local) (h : u.1.val = 0 ∨ u.1.val = 11) (c : Colour) :
    cap (feature u) c .goBetween = 0 := by
  have hn : ¬ HasSlot u.1 c .goBetween := by
    simp only [HasSlot]
    omega
  cases c <;> exact localCap_no_slot u _ _ hn

theorem goBetween_lance_zero (u : Local) (h : u.1.val = 3 ∨ u.1.val = 8) (c : Colour) :
    cap (feature u) c .lance = 0 ∧ cap (feature u) c .chariot = 0 := by
  have hn (k : Kind) (hk : k = .lance ∨ k = .chariot) : ¬ HasSlot u.1 c k := by
    rcases hk with rfl | rfl <;> simp only [HasSlot] <;> omega
  cases c <;> exact ⟨localCap_no_slot u _ _ (hn _ (.inl rfl)),localCap_no_slot u _ _ (hn _ (.inr rfl))⟩

end ChuShogi.GroupedFiles
