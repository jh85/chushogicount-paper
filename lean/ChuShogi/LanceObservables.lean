import ChuShogi.FileGame

/-! The lance provider's observables. Only the projection and singleton
promoted-state queries are required by the candidate counter. -/
namespace ChuShogi.LanceObservables
open FileGame Promotion
set_option maxRecDepth 1000000
set_option maxHeartbeats 200000000

def slots : List Slot :=
  [(.black,.lance),(.black,.chariot),(.black,.pawn),(.white,.pawn),(.white,.chariot),(.white,.lance)]
def initial : State := [1,2,4,9,11,12]
abbrev R := FiniteSearch.Reach (next slots) initial

def capture (u : List Nat) : State := u.map (Fin.ofNat 14)
def mark (u : List Nat) (i : Fin 6) : State := (capture u).set i.val 13
def label (i : Fin 6) : Slot := slots[i.val]
def valid (u : List Nat) : Prop := OrderedFile.Admissible OrderedFile.lanceSlots u
def eligible (u : List Nat) (i : Fin 6) : Prop :=
  Eligible (uFile slots (capture u)) (label i).1 (label i).2

instance (u : List Nat) : Decidable (valid u) := by
  unfold valid OrderedFile.Admissible
  infer_instance
instance (u : List Nat) (i : Fin 6) : Decidable (eligible u i) := inferInstanceAs
  (Decidable (Eligible (uFile slots (capture u)) (label i).1 (label i).2))

theorem slots_ordered : slots.map orderedSlot = OrderedFile.lanceSlots := rfl

theorem valid_mem (u : List Nat) : valid u ↔ u ∈ OrderedFile.enumerate 0 OrderedFile.lanceSlots :=
  (OrderedFile.exact_enumeration _).2 u |>.symm

theorem bounded_entries (ls : List OrderedFile.Slot) (u : List Nat)
    (h : OrderedFile.Bounded ls u) : ∀ r ∈ u, r ≤ 12 := by
  induction ls generalizing u with
  | nil => subst u; simp
  | cons s ls ih =>
    obtain ⟨r,tail,rfl,hr,ht⟩ := h
    intro t hmem
    rcases List.mem_cons.mp hmem with rfl | hmem
    · rcases hr with rfl | hr
      · omega
      · exact hr.2.1
    · exact ih tail ht t hmem

theorem capture_projection (u : List Nat) (hu : valid u) : (capture u).map shown = u := by
  rw [capture,List.map_map]
  calc
    u.map (shown ∘ Fin.ofNat 14) = u.map id := by
      apply List.map_congr_left
      intro r hr
      have hb := bounded_entries _ _ hu.1 r hr
      simp [shown,Fin.ofNat,Nat.mod_eq_of_lt (show r < 14 by omega),hb]
    _ = u := List.map_id u

theorem projection_rows (ls : List Slot) (st tt : State) (h : st.map shown = tt.map shown)
    (c : Colour) (k : Kind) :
    (((ls.zip st).filter fun (s,_) => decide (s=(c,k))).map fun (_,r) => shown r) =
      (((ls.zip tt).filter fun (s,_) => decide (s=(c,k))).map fun (_,r) => shown r) := by
  induction ls generalizing st tt with
  | nil => simp
  | cons s ls ih =>
    cases st with
    | nil => cases tt <;> simp_all
    | cons r st =>
      cases tt with
      | nil => simp at h
      | cons q tt =>
        have he := List.cons.inj h
        by_cases hs : s=(c,k)
        · simp [hs,he.1,ih st tt he.2]
        · simp [hs,ih st tt he.2]

theorem uFile_projection (st tt : State) (h : st.map shown = tt.map shown) :
    uFile slots st = uFile slots tt := by
  funext c k
  exact congrArg List.sum (projection_rows slots st tt h c k)

theorem list_six {A : Type} (xs : List A) (h : xs.length=6) :
    ∃ a b c d e f, xs=[a,b,c,d,e,f] := by
  rcases xs with _ | ⟨a,xs⟩; · simp at h
  rcases xs with _ | ⟨b,xs⟩; · simp at h
  rcases xs with _ | ⟨c,xs⟩; · simp at h
  rcases xs with _ | ⟨d,xs⟩; · simp at h
  rcases xs with _ | ⟨e,xs⟩; · simp at h
  rcases xs with _ | ⟨f,xs⟩; · simp at h
  have ht : xs=[] := List.eq_nil_of_length_eq_zero (by simpa using h)
  subst xs
  exact ⟨a,b,c,d,e,f,rfl⟩

theorem uFile_at (st : State) (hlen : st.length=6) (i : Fin 6) :
    uFile slots st (label i).1 (label i).2 = shown st[i.val] := by
  obtain ⟨a,b,c,d,e,f,rfl⟩ := list_six st hlen
  rcases i with ⟨i,hi⟩
  have hs : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [uFile,slots,label]

theorem marked_eligible (st : State) (hc : Classified slots st) (i : Fin 6)
    (hi : st[i.val]? = some 13) : Eligible (uFile slots st) (label i).1 (label i).2 := by
  have hl : st.length=6 := hc.1
  have hm : (label i,(13 : Fin 14)) ∈ slots.zip st := by
    obtain ⟨a,b,c,d,e,f,rfl⟩ := list_six st hl
    rcases i with ⟨i,hi'⟩
    have hs : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 := by omega
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> simpa [slots,label,eq_comm] using hi
  have h := (List.all_eq_true.mp hc.2.2.1) _ hm
  have hv : (13 : Fin 14).val=13 := rfl
  simpa only [decide_eq_true_eq,hv,ne_eq,not_true_eq_false,false_or] using h

end ChuShogi.LanceObservables
