import ChuShogi.ConfinedMaterial

/-! Completion constraints reduced to the concrete summary and canonical free
pieces. The confined I9 inequalities are proved redundant, not removed by fiat. -/
namespace ChuShogi.Completion
open Specification Promotion ConcreteDP BoardDecomposition SummaryBridge ConfinedMaterial

 theorem free_at (b : Board) (s : Square) (c : Colour) (r : Role) (hr : isConfined r = false) :
    free b s = some (c,r) ↔ b s = some (c,r) := by
  simp [free,Option.filter_eq_some_iff,hr]

theorem free_count (b : Board) (c : Colour) (r : Role) (hr : isConfined r = false) (p : Square → Bool) :
    countWhere (free b) c r p = countWhere b c r p := by
  simp only [countWhere,free_at b _ c r hr]

theorem free_number (b : Board) (c : Colour) (r : Role) (hr : isConfined r = false) :
    number (free b) c r = number b c r := free_count b c r hr _

theorem free_confined_zero (b : Board) (c : Colour) (k : Kind) :
    number (free b) c (.native (kindBase k)) = 0 := by
  have h (s : Square) : free b s ≠ some (c,.native (kindBase k)) := by
    intro hs
    have he := (split_properties b).2.1 s _ hs
    rw [isConfined_kind] at he
    cases he
  simp only [number,countWhere]
  have he : (squares.filter fun s => decide (free b s = some (c,.native (kindBase k))) && true) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro s _
    simp [h s]
  rw [he]
  rfl

theorem free_number_eq (b : Board) (c : Colour) (r : Role) :
    number (free b) c r = if isConfined r then 0 else number b c r := by
  cases hr : isConfined r with
  | false => simpa only [hr,Bool.false_eq_true,ite_false] using free_number b c r hr
  | true =>
    obtain ⟨k,rfl⟩ := (isConfined_iff r).mp hr
    simpa only [hr,ite_true] using free_confined_zero b c k

theorem I9_to_free (b : Board) (h : I9 b) : I9 (free b) := by
  intro c
  have hc := h c
  refine ⟨?_,?_⟩
  · intro k
    have hp := hc.1 k
    cases k <;> simp [Separate.base,initialSeparate,free_number_eq,isConfined] at hp ⊢ <;> omega
  · simpa [free_number_eq,isConfined] using hc.2

theorem I9_from_free (b : Board) (h1 : I1 b) (h4 : I4 b) (h5 : I5 b) (h : I9 (free b)) : I9 b := by
  intro c
  have hc := h c
  refine ⟨?_,?_⟩
  · intro k
    have hp := hc.1 k
    cases k <;>
      simp only [Separate.base,initialSeparate] at hp ⊢ <;>
      first
      | (simpa [free_number_eq,isConfined] using hp)
      | (first
          | simpa [kindBase,kindSeparate,promotedNumber,stock] using confined_material b h1 h4 h5 c .pawn
          | simpa [kindBase,kindSeparate,promotedNumber,stock] using confined_material b h1 h4 h5 c .lance
          | simpa [kindBase,kindSeparate,promotedNumber,stock] using confined_material b h1 h4 h5 c .chariot
          | simpa [kindBase,kindSeparate,promotedNumber,stock] using confined_material b h1 h4 h5 c .goBetween)
  · simpa [free_number_eq,isConfined] using hc.2

/-- Concrete I9 sufficiency: no unpromoted type-count summary is required. -/
theorem I9_free_iff (b : Board) (h1 : I1 b) (h4 : I4 b) (h5 : I5 b) : I9 b ↔ I9 (free b) :=
  ⟨I9_to_free b,I9_from_free b h1 h4 h5⟩

theorem candidate_reduced (b : Board) : Candidate b ↔
    I1 b ∧ I2 b ∧ I3 b ∧ I4 b ∧ I5 b ∧ I6 b ∧ I7 b ∧ I8 b ∧ I9 (free b) := by
  constructor
  · rintro ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩
    exact ⟨h1,h2,h3,h4,h5,h6,h7,h8,I9_to_free b h9⟩
  · rintro ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩
    exact ⟨h1,h2,h3,h4,h5,h6,h7,h8,I9_from_free b h1 h4 h5 h9⟩

def Bounds (s : Summary) (f : Board) : Prop :=
  promotedNumber f .black .pawn + promotedNumber f .white .pawn ≤ s.joint ∧
  ∀ c k, k ≠ .pawn → promotedNumber f c k ≤ cap s c k

def FreeConditions (s : Summary) (f : Board) : Prop :=
  Bounds s f ∧ I6 f ∧ I7 f ∧ I8 f ∧ I9 f

def Completes (u f : Board) : Prop := OnlyFree f ∧ Disjoint u f ∧ Candidate (merge u f)

theorem merge_number_free (u f : Board) (hu : OnlyConfined u) (hf : OnlyFree f) (hd : Disjoint u f)
    (c : Colour) (r : Role) (hr : isConfined r = false) :
    number (merge u f) c r = number f c r := by
  rw [← free_number (merge u f) c r hr,(split_merge u f hu hf hd).2]

theorem merge_count_free (u f : Board) (hu : OnlyConfined u) (hf : OnlyFree f) (hd : Disjoint u f)
    (c : Colour) (r : Role) (hr : isConfined r = false) (p : Square → Bool) :
    countWhere (merge u f) c r p = countWhere f c r p := by
  rw [← free_count (merge u f) c r hr p,(split_merge u f hu hf hd).2]

theorem merge_unpromoted (u f : Board) (hu : OnlyConfined u) (hf : OnlyFree f) (hd : Disjoint u f) :
    unpromoted (merge u f) = unpromoted u := by
  rw [← unpromoted_confined (merge u f),(split_merge u f hu hf hd).1]

theorem merge_I1 (u f : Board) (hu : OnlyConfined u) (hf : OnlyFree f) (hd : Disjoint u f) :
    I1 (merge u f) ↔ I1 u := by
  rw [← confined_I1,(split_merge u f hu hf hd).1]

theorem merge_I2 (u f : Board) (hu : OnlyConfined u) (hf : OnlyFree f) (hd : Disjoint u f) :
    I2 (merge u f) ↔ I2 u := by
  rw [← confined_I2,(split_merge u f hu hf hd).1]

theorem merge_I3 (u f : Board) (hu : OnlyConfined u) (hf : OnlyFree f) (hd : Disjoint u f) :
    I3 (merge u f) ↔ I3 u := by
  rw [← confined_I3,(split_merge u f hu hf hd).1]

theorem merge_I6 (u f : Board) (hu : OnlyConfined u) (hf : OnlyFree f) (hd : Disjoint u f) :
    I6 (merge u f) ↔ I6 f := by
  simp only [I6,merge_count_free u f hu hf hd _ (.native .bishop) rfl]

theorem merge_I7 (u f : Board) (hu : OnlyConfined u) (hf : OnlyFree f) (hd : Disjoint u f) :
    I7 (merge u f) ↔ I7 f := by
  have hh (s : Square) (c : Colour) : merge u f s = some (c,.native .kirin) ↔ f s = some (c,.native .kirin) := by
    rw [← free_at (merge u f) s c (.native .kirin) rfl,(split_merge u f hu hf hd).2]
  simp only [I7,hh]

theorem merge_royal (u f : Board) (hu : OnlyConfined u) (hf : OnlyFree f) (hd : Disjoint u f) (c : Colour) :
    hasRoyal (merge u f) c ↔ hasRoyal f c := by
  simp only [hasRoyal,merge_number_free u f hu hf hd c (.native .king) rfl]

/-- Exact completion specification on the existing concrete summary. -/
theorem completes_iff (u f : Board) (hu : OnlyConfined u) (h1 : I1 u) (h2 : I2 u) (h3 : I3 u) :
    Completes u f ↔ OnlyFree f ∧ Disjoint u f ∧ FreeConditions (boardSummary u) f := by
  unfold Completes
  constructor
  · rintro ⟨hf,hd,hc⟩
    have hm1 := (merge_I1 u f hu hf hd).mpr h1
    have hs : boardSummary (merge u f) = boardSummary u := by
      unfold boardSummary boardTuple boardLocal
      rw [merge_unpromoted u f hu hf hd]
    have hb := (I4_I5_summary (merge u f) hm1).mp ⟨hc.2.2.2.1,hc.2.2.2.2.1⟩
    simp only [hs,promotedNumber,merge_number_free u f hu hf hd _ (.promoted _) rfl] at hb
    refine ⟨hf,hd,hb,(merge_I6 u f hu hf hd).mp hc.2.2.2.2.2.1,
      (merge_I7 u f hu hf hd).mp hc.2.2.2.2.2.2.1,
      (merge_royal u f hu hf hd .white).mp hc.2.2.2.2.2.2.2.1,?_⟩
    rw [← (split_merge u f hu hf hd).2]
    exact I9_to_free _ hc.2.2.2.2.2.2.2.2
  · rintro ⟨hf,hd,hb,h6,h7,h8,h9⟩
    have hm1 := (merge_I1 u f hu hf hd).mpr h1
    have hs : boardSummary (merge u f) = boardSummary u := by
      unfold boardSummary boardTuple boardLocal
      rw [merge_unpromoted u f hu hf hd]
    have hbound : I4 (merge u f) ∧ I5 (merge u f) := by
      apply (I4_I5_summary (merge u f) hm1).mpr
      simpa only [Bounds,hs,promotedNumber,merge_number_free u f hu hf hd _ (.promoted _) rfl] using hb
    refine ⟨hf,hd,(candidate_reduced _).mpr ⟨hm1,(merge_I2 u f hu hf hd).mpr h2,
      (merge_I3 u f hu hf hd).mpr h3,hbound.1,hbound.2,
      (merge_I6 u f hu hf hd).mpr h6,(merge_I7 u f hu hf hd).mpr h7,
      (merge_royal u f hu hf hd .white).mpr h8,?_⟩⟩
    rw [(split_merge u f hu hf hd).2]
    exact h9

end ChuShogi.Completion
