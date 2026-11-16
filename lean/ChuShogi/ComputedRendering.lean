import ChuShogi.FiniteLookup
import ChuShogi.StructuralDecomposition

/-! Computed confined rendering. All searches range over the twelve tuple
entries or the eight actual confined labels, never over complete Boards. -/
namespace ChuShogi.ComputedRendering
open Specification Promotion ConcreteDP BoardDecomposition Rendering TupleRendering

def slots (us : List Local) : Slots := fun x =>
  match us.find? (fun v => decide (v.1=x)) with
  | some v => localU v
  | none => fun _ _ => 0

theorem slots_eq (us : List Local) (h : ConcreteDP.Valid us) : slots us=TupleRendering.decode us h := by
  funext x
  have hs : (us.find? (fun v => decide (v.1=x))).isSome=true :=
    List.find?_isSome.mpr (by obtain ⟨v,hv,hx⟩ := entry_exists us h x; exact ⟨v,hv,by simp [hx]⟩)
  cases he : us.find? (fun v => decide (v.1=x)) with
  | none => simp [he] at hs
  | some v =>
    have hv := List.mem_of_find?_eq_some he
    have hx : v.1=x := of_decide_eq_true (List.find?_some (p := fun v : Local => decide (v.1=x)) he)
    have hu := entry_unique us h v (entry us h x) hv (entry_spec us h x).1 (hx.trans (entry_spec us h x).2.symm)
    simp only [slots,he,TupleRendering.decode,hu]

def allLabels : List Label :=
  [(.black,.pawn),(.black,.goBetween),(.black,.lance),(.black,.chariot),
   (.white,.pawn),(.white,.goBetween),(.white,.lance),(.white,.chariot)]

theorem allLabels_complete (l : Label) : l ∈ allLabels := by rcases l with ⟨c,k⟩; cases c <;> cases k <;> decide

instance (u : Slots) (s : Square) (l : Label) : Decidable (At u s l) := inferInstanceAs (Decidable (_ ∧ _))

def render (u : Slots) : Board := fun s =>
  (allLabels.find? (fun l => decide (At u s l))).map labelPiece

theorem render_eq (u : Slots) (hu : SlotValid u) : render u=Rendering.render u := by
  funext s
  cases he : allLabels.find? (fun l => decide (At u s l)) with
  | some l =>
    have hl : At u s l := of_decide_eq_true (List.find?_some (p := fun l => decide (At u s l)) he)
    simp only [render,he,Option.map_some]
    exact ((render_at u hu s l).mpr hl).symm
  | none =>
    have hn : ¬∃ l, At u s l := by
      rintro ⟨l,hl⟩
      have hh := List.find?_eq_none.mp he l (allLabels_complete l)
      simp [hl] at hh
    simp [render,he,Rendering.render,hn]

def tuple (us : List Local) : Board := render (slots us)

theorem tuple_eq (us : List Local) (h : ConcreteDP.Valid us) : tuple us=StructuralDecomposition.renderAny us := by
  rw [tuple,slots_eq us h,render_eq _ (decode_valid us h),StructuralDecomposition.renderAny_eq us h]
  rfl

end ChuShogi.ComputedRendering
