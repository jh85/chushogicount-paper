import ChuShogi.SummaryBridge

/-! Independent slot placements and their canonical Board rendering. Classical
choice constructs a mathematical inverse; no numerical counter uses it. -/
namespace ChuShogi.Rendering
open Specification Promotion ConcreteDP BoardDecomposition
set_option maxRecDepth 4096

abbrev Slots := Fin 12 → UFile

/-- Fixed original files, present-rank bounds and strict original-slot order. -/
def SlotValid (u : Slots) : Prop :=
  (∀ x c k, ¬ HasSlot x c k → u x c k = 0) ∧
  (∀ x c k, u x c k = 0 ∨ OrderedFile.RankAllowed (orderedLabel (c,k)) (u x c k)) ∧
  (∀ x c d k l, confinedStart c k < confinedStart d l →
    u x c k ≠ 0 → u x d l ≠ 0 → u x c k < u x d l)

def At (u : Slots) (s : Square) (l : Label) : Prop :=
  HasSlot s.1 l.1 l.2 ∧ u s.1 l.1 l.2 = rank s

def labelPiece (l : Label) : Piece := (l.1,.native (kindBase l.2))

theorem start_injective (a b : Label) (h : confinedStart a.1 a.2 = confinedStart b.1 b.2) : a = b := by
  rcases a with ⟨c,k⟩
  rcases b with ⟨d,l⟩
  cases c <;> cases d <;> cases k <;> cases l <;> simp_all [confinedStart]

theorem labelPiece_injective (a b : Label) (h : labelPiece a = labelPiece b) : a = b := by
  rcases a with ⟨c,k⟩
  rcases b with ⟨d,l⟩
  cases c <;> cases d <;> cases k <;> cases l <;> simp_all [labelPiece,kindBase]

theorem at_unique (u : Slots) (h : SlotValid u) (s : Square) (a b : Label)
    (ha : At u s a) (hb : At u s b) : a = b := by
  apply Classical.byContradiction
  intro hn
  have hs : confinedStart a.1 a.2 ≠ confinedStart b.1 b.2 := fun he => hn (start_injective a b he)
  have han : u s.1 a.1 a.2 ≠ 0 := by rw [ha.2]; unfold rank; omega
  have hbn : u s.1 b.1 b.2 ≠ 0 := by rw [hb.2]; unfold rank; omega
  rcases Nat.lt_or_gt_of_ne hs with hl | hr
  · have he := h.2.2 s.1 a.1 b.1 a.2 b.2 hl han hbn
    rw [ha.2,hb.2] at he
    omega
  · have he := h.2.2 s.1 b.1 a.1 b.2 a.2 hr hbn han
    rw [ha.2,hb.2] at he
    omega

noncomputable def render (u : Slots) : Board := by
  classical
  exact fun s => if h : ∃ l, At u s l then some (labelPiece (Classical.choose h)) else none

theorem render_at (u : Slots) (h : SlotValid u) (s : Square) (l : Label) :
    render u s = some (labelPiece l) ↔ At u s l := by
  unfold render
  split
  · rename_i he
    have hc := Classical.choose_spec he
    constructor
    · intro hp
      have hl := labelPiece_injective _ _ (Option.some.inj hp)
      simpa only [hl] using hc
    · intro hl
      rw [at_unique u h s _ _ hc hl]
  · rename_i he
    constructor
    · intro hp; cases hp
    · intro ha; exact False.elim (he ⟨l,ha⟩)

theorem render_onlyConfined (u : Slots) : OnlyConfined (render u) := by
  intro s p hp
  unfold render at hp
  split at hp
  · cases Option.some.inj hp
    exact isConfined_kind _
  · cases hp

theorem squares_nodup : squares.Nodup := by decide

theorem square_eq (s t : Square) (hf : s.1 = t.1) (hr : rank s = rank t) : s = t := by
  apply Prod.ext hf
  apply Fin.ext
  unfold rank at hr
  omega

theorem short_of_unique {A : Type} (xs : List A) (hn : xs.Nodup)
    (hu : ∀ a ∈ xs, ∀ b ∈ xs, a = b) : xs.length ≤ 1 := by
  cases xs with
  | nil => simp
  | cons a xs =>
    have ht : xs = [] := by
      cases xs with
      | nil => rfl
      | cons b bs =>
        have he := hu a (by simp) b (by simp)
        have hm : a ∈ b :: bs := by simp [he]
        exact False.elim ((List.nodup_cons.mp hn).1 hm)
    simp [ht]

theorem render_I1 (u : Slots) (h : SlotValid u) : I1 (render u) := by
  constructor
  · intro s c k hp
    exact ((render_at u h s (c,k)).mp hp).1
  · intro x c k
    rw [← slotSquares_length]
    apply short_of_unique _ (squares_nodup.filter _)
    intro s hs t ht
    have hs' : s.1 = x ∧ render u s = some (labelPiece (c,k)) :=
      of_decide_eq_true (List.mem_filter.mp hs).2
    have ht' : t.1 = x ∧ render u t = some (labelPiece (c,k)) :=
      of_decide_eq_true (List.mem_filter.mp ht).2
    have hsr := ((render_at u h s (c,k)).mp hs'.2).2
    have htr := ((render_at u h t (c,k)).mp ht'.2).2
    apply square_eq s t (hs'.1.trans ht'.1.symm)
    rw [← hsr,← htr,hs'.1,ht'.1]

theorem render_I2 (u : Slots) (h : SlotValid u) : I2 (render u) := by
  intro s t c d k l hs ht hf ho
  have hsr := ((render_at u h s (c,k)).mp hs).2
  have htr := ((render_at u h t (d,l)).mp ht).2
  have hsn : u s.1 c k ≠ 0 := by rw [hsr]; unfold rank; omega
  have htn : u s.1 d l ≠ 0 := by rw [hf,htr]; unfold rank; omega
  have he := h.2.2 s.1 c d k l ho hsn htn
  rwa [hsr,hf,htr] at he

theorem render_I3 (u : Slots) (h : SlotValid u) : I3 (render u) := by
  constructor
  · intro s hs
    have hr := ((render_at u h s (.black,.pawn)).mp hs).2
    have hn : u s.1 .black .pawn ≠ 0 := by rw [hr]; unfold rank; omega
    have hb := (h.2.1 s.1 .black .pawn).resolve_left hn
    rw [hr] at hb
    exact hb.2.2.1 rfl
  · intro s hs
    have hr := ((render_at u h s (.white,.pawn)).mp hs).2
    have hn : u s.1 .white .pawn ≠ 0 := by rw [hr]; unfold rank; omega
    have hb := (h.2.1 s.1 .white .pawn).resolve_left hn
    rw [hr] at hb
    exact hb.2.2.2 rfl

/-- Every independently valid slot placement has exactly the requested projection. -/
theorem unpromoted_render (u : Slots) (h : SlotValid u) : unpromoted (render u) = u := by
  funext x c k
  by_cases hz : u x c k = 0
  · apply Classical.byContradiction
    intro hn
    have hp : unpromoted (render u) x c k ≠ 0 := by simpa [hz] using hn
    obtain ⟨s,hx,hs,hr⟩ := unpromoted_present _ (render_I1 u h) x c k hp
    have he := ((render_at u h s (c,k)).mp hs).2
    rw [hx,hz] at he
    unfold rank at he
    omega
  · have hb := (h.2.1 x c k).resolve_left hz
    let s : Square := (x,⟨u x c k - 1,by have h1 := hb.1; have h2 := hb.2.1; omega⟩)
    have hr : rank s = u x c k := by dsimp [s,rank]; have h1 := hb.1; omega
    have hs : HasSlot x c k := by
      apply Classical.byContradiction
      intro hn
      exact hz (h.1 x c k hn)
    have hp := (render_at u h s (c,k)).mpr ⟨hs,hr.symm⟩
    have he := unpromoted_at _ (render_I1 u h) s c k hp
    exact he.trans hr

theorem slotValid_of_board (b : Board) (h1 : I1 b) (h2 : I2 b) (h3 : I3 b) : SlotValid (unpromoted b) := by
  refine ⟨absent_slot_zero b h1,unpromoted_bound b h1 h3,?_⟩
  intro x c d k l ho hn hm
  obtain ⟨s,hs,hp,hr⟩ := unpromoted_present b h1 x c k hn
  obtain ⟨t,ht,hq,hsr⟩ := unpromoted_present b h1 x d l hm
  rw [hr,hsr]
  exact h2 s t c d k l hp hq (hs.trans ht.symm) ho

/-- Both directions of the Board/slot-placement inverse are proved. -/
theorem render_projection (b : Board) (hc : OnlyConfined b) (h1 : I1 b) (h2 : I2 b) (h3 : I3 b) :
    render (unpromoted b) = b := by
  have hv := slotValid_of_board b h1 h2 h3
  exact confined_projection_injective _ b (render_I1 _ hv) h1
    (render_onlyConfined _) hc (unpromoted_render _ hv)

end ChuShogi.Rendering
