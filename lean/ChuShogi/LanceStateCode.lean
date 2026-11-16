import ChuShogi.LanceObservables

/-! Numeric-key certificate lookup for the six-slot lance provider. Codes are
proved injective on exactly the state shape needed here; no stronger abstract
game equivalence is introduced. Stored keys are checked against actual states.
-/
namespace ChuShogi.LanceStateCode
open FileGame FiniteSearch LanceObservables

theorem code_injective (s t : State) (hs : s.length=6) (ht : t.length=6)
    (h : code s=code t) : s=t := by
  obtain ⟨a,b,c,d,e,f,rfl⟩ := list_six s hs
  obtain ⟨a',b',c',d',e',f',rfl⟩ := list_six t ht
  dsimp [code] at h
  have ha : a=a' := Fin.ext (by omega)
  have hb : b=b' := Fin.ext (by omega)
  have hc : c=c' := Fin.ext (by omega)
  have hd : d=d' := Fin.ext (by omega)
  have he : e=e' := Fin.ext (by omega)
  have hf : f=f' := Fin.ext (by omega)
  simp only [ha,hb,hc,hd,he,hf]

inductive Tree where
  | empty
  | node (key : Nat) (state : State) (left right : Tree)

def All (p : State → Prop) : Tree → Prop
  | .empty => True
  | .node _ s l r => p s ∧ All p l ∧ All p r

def Correct : Tree → Prop
  | .empty => True
  | .node k s l r => k=code s ∧ s.length=6 ∧ Correct l ∧ Correct r

instance allDecidable (p : State → Prop) [DecidablePred p] (tree : Tree) : Decidable (All p tree) :=
  match tree with
  | .empty => isTrue trivial
  | .node _ _ l r =>
    let _ := allDecidable p l
    let _ := allDecidable p r
    inferInstanceAs (Decidable (_ ∧ _ ∧ _))

instance correctDecidable (tree : Tree) : Decidable (Correct tree) :=
  match tree with
  | .empty => isTrue trivial
  | .node _ _ l r =>
    let _ := correctDecidable l
    let _ := correctDecidable r
    inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def contains (key : Nat) : Tree → Bool
  | .empty => false
  | .node k _ l r => if key=k then true else if key<k then contains key l else contains key r

theorem contains_all (p : State → Prop) (tree : Tree) (hc : Correct tree) (hp : All p tree)
    (s : State) (hs : s.length=6) (h : contains (code s) tree=true) : p s := by
  induction tree with
  | empty => simp [contains] at h
  | node k t l r il ir =>
    simp only [contains] at h
    split at h
    · rename_i he
      have ht : s=t := code_injective s t hs hc.2.1 (he.trans hc.1)
      subst t
      exact hp.1
    · split at h
      · exact il hc.2.2.1 hp.2.1 h
      · exact ir hc.2.2.2 hp.2.2 h

theorem next_length (ls : List Slot) (s t : State) (ht : t ∈ next ls s) : t.length=s.length := by
  unfold next at ht
  obtain ⟨entry,_,ht⟩ := List.mem_flatMap.mp ht
  rcases entry with ⟨⟨slot,r⟩,i⟩
  dsimp only at ht
  split at ht
  · simp only [List.mem_append,List.mem_singleton,List.mem_flatMap] at ht
    rcases ht with rfl | ⟨r,_,ht⟩
    · simp
    · rcases ht with rfl | ht
      · simp
      · split at ht
        · have he := List.mem_singleton.mp ht
          subst t
          simp
        · cases ht
  · cases ht

theorem reach_length (ls : List Slot) (i s : State) (h : Reach (next ls) i s) : s.length=i.length := by
  induction h with
  | initial => rfl
  | step _ ht ih => exact (next_length _ _ _ ht).trans ih

theorem reach_contained (ls : List Slot) (i : State) (hi : i.length=6) (tree : Tree) (hc : Correct tree)
    (h0 : contains (code i) tree=true)
    (hclose : All (fun s => (next ls s).all (fun t => contains (code t) tree)=true) tree)
    (s : State) (hr : Reach (next ls) i s) : contains (code s) tree=true := by
  induction hr with
  | initial => exact h0
  | @step s t hs ht ih =>
    have hlen : s.length=6 := (reach_length _ _ _ hs).trans hi
    exact (List.all_eq_true.mp (contains_all _ tree hc hclose s hlen ih)) t ht

theorem bounded_length (ls : List OrderedFile.Slot) (u : List Nat) (h : OrderedFile.Bounded ls u) :
    u.length=ls.length := by
  induction ls generalizing u with
  | nil => subst u; rfl
  | cons s ls ih =>
    obtain ⟨r,tail,rfl,_,ht⟩ := h
    simp [ih tail ht]

theorem capture_length (u : List Nat) (h : valid u) : (capture u).length=6 := by
  simpa [capture,OrderedFile.lanceSlots] using bounded_length _ _ h.1

theorem mark_length (u : List Nat) (h : valid u) (i : Fin 6) : (mark u i).length=6 := by
  rw [mark,List.length_set,capture_length u h]

end ChuShogi.LanceStateCode
