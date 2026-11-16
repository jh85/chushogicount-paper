import ChuShogi.TableInvariant

/-! Actual support of capacity fields in the three constructed file tables.
This discharges the disjoint-type premise for special polynomial grouping. -/
namespace ChuShogi.GroupCapacity
open Specification Promotion ConcreteDP SummaryBridge GroupedFiles TableInvariant

def ZeroFor (K : Kind → Prop) (s : Summary) : Prop := ∀ c k, K k → cap s c k = 0

theorem cap_add (s t : Summary) (c : Colour) (k : Kind) : cap (add s t) c k = cap s c k+cap t c k := by
  cases c <;> cases k <;> rfl

theorem cap_erase (s : Summary) (c : Colour) (k : Kind) : cap (CompactSummary.erase s) c k = cap s c k := by
  cases c <;> cases k <;> rfl

theorem zero_init (K : Kind → Prop) : ZeroFor K zero := by
  intro c k _; cases c <;> cases k <;> rfl

theorem zero_add (K : Kind → Prop) (s t : Summary) (hs : ZeroFor K s) (ht : ZeroFor K t) : ZeroFor K (add s t) := by
  intro c k hk
  rw [cap_add,hs c k hk,ht c k hk]

theorem feature_erase (u : Local) (K : Kind → Prop) (h : ZeroFor K (feature u)) :
    ZeroFor K (CompactSummary.compactFeature u) := by
  intro c k hk
  rw [CompactSummary.compactFeature,cap_erase]
  exact h c k hk

theorem lance_features : ∀ xs ∈ lanceFiles, ∀ u ∈ xs,
    ZeroFor (fun k => k = .goBetween) (CompactSummary.compactFeature u) := by
  intro xs hxs u hu
  apply feature_erase
  intro c k hk; subst k
  simp only [lanceFiles,List.mem_cons,List.not_mem_nil,or_false] at hxs
  rcases hxs with rfl | rfl
  · have he := (localConfigs_iff 11 u).mp hu |>.1
    apply lance_goBetween_zero u _ c
    exact .inr (congrArg Fin.val he)
  · have he := (localConfigs_iff 0 u).mp hu |>.1
    apply lance_goBetween_zero u _ c
    exact .inl (congrArg Fin.val he)

theorem goBetween_features : ∀ xs ∈ goBetweenFiles, ∀ u ∈ xs,
    ZeroFor (fun k => k = .lance ∨ k = .chariot) (CompactSummary.compactFeature u) := by
  intro xs hxs u hu
  apply feature_erase
  have hp : u.1.val = 3 ∨ u.1.val = 8 := by
    simp only [goBetweenFiles,List.mem_cons,List.not_mem_nil,or_false] at hxs
    rcases hxs with rfl | rfl
    · exact .inr (congrArg Fin.val ((localConfigs_iff 8 u).mp hu).1)
    · exact .inl (congrArg Fin.val ((localConfigs_iff 3 u).mp hu).1)
  intro c k hk
  rcases hk with rfl | rfl
  · exact (goBetween_lance_zero u hp c).1
  · exact (goBetween_lance_zero u hp c).2

theorem plain_features : ∀ xs ∈ plainFiles, ∀ u ∈ xs,
    ZeroFor (fun k => k ≠ .pawn) (CompactSummary.compactFeature u) := by
  intro xs hxs u hu
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hxs
  have he := (localConfigs_iff x u).mp hu |>.1
  have hp : x.val ≠ 0 ∧ x.val ≠ 11 ∧ x.val ≠ 3 ∧ x.val ≠ 8 := by
    exact of_decide_eq_true (List.mem_filter.mp hx).2
  apply feature_erase
  intro c k hk
  apply plain_cap_zero u _ c k hk
  rw [he]
  exact hp

theorem lance_support : Keys (ZeroFor (fun k => k = .goBetween)) lanceTable :=
  dp_keys _ zero add CompactSummary.compactFeature lanceFiles (zero_init _) (zero_add _) lance_features

theorem goBetween_support : Keys (ZeroFor (fun k => k = .lance ∨ k = .chariot)) goBetweenTable :=
  dp_keys _ zero add CompactSummary.compactFeature goBetweenFiles (zero_init _) (zero_add _) goBetween_features

theorem plain_support : Keys (ZeroFor (fun k => k ≠ .pawn)) plainTable :=
  dp_keys _ zero add CompactSummary.compactFeature plainFiles (zero_init _) (zero_add _) plain_features

theorem feature_cap_le_one (u : Local) (c : Colour) (k : Kind) :
    cap (CompactSummary.compactFeature u) c k ≤ 1 := by
  rw [CompactSummary.compactFeature,cap_erase]
  cases c <;> cases k <;> simp only [feature,cap,localCap,bit] <;> split <;> decide

theorem table_cap_bound (fs : List (List Local)) (c : Colour) (k : Kind) :
    Keys (fun s => cap s c k ≤ fs.length) (WeightedDP.dp zero add CompactSummary.compactFeature fs) :=
  dp_bound (fun s => cap s c k) zero add CompactSummary.compactFeature fs
    (by cases c <;> cases k <;> rfl) (fun s t => cap_add s t c k)
    (fun _ _ u _ => feature_cap_le_one u c k)

theorem lance_cap_bound (c : Colour) (k : Kind) : Keys (fun s => cap s c k ≤ 2) lanceTable :=
  table_cap_bound lanceFiles c k

theorem goBetween_cap_bound (c : Colour) (k : Kind) : Keys (fun s => cap s c k ≤ 2) goBetweenTable :=
  table_cap_bound goBetweenFiles c k

def PawnShape (s : Summary) : Prop := s.cb=s.joint ∧ s.cw=s.joint

theorem pawn_shape_add (s t : Summary) (hs : PawnShape s) (ht : PawnShape t) : PawnShape (add s t) := by
  change s.cb+t.cb=s.joint+t.joint ∧ s.cw+t.cw=s.joint+t.joint
  rw [hs.1,ht.1,hs.2,ht.2]
  exact ⟨rfl,rfl⟩

theorem table_pawn_shape (fs : List (List Local)) :
    Keys PawnShape (WeightedDP.dp zero add CompactSummary.compactFeature fs) :=
  dp_keys PawnShape zero add CompactSummary.compactFeature fs ⟨rfl,rfl⟩ pawn_shape_add
    (fun _ _ _ _ => ⟨rfl,rfl⟩)

end ChuShogi.GroupCapacity
