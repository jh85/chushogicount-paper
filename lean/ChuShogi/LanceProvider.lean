import ChuShogi.LanceCertificate
import ChuShogi.ConcreteDP

/-! Provider-level projected and singleton correspondence. -/
namespace ChuShogi.LanceProvider
open FileGame Promotion LanceObservables LanceCertificate

theorem bounded_length (ls : List OrderedFile.Slot) (u : List Nat) (h : OrderedFile.Bounded ls u) :
    u.length=ls.length := by
  induction ls generalizing u with
  | nil => subst u; rfl
  | cons s ls ih =>
    obtain ⟨r,tail,rfl,_,ht⟩ := h
    simp [ih tail ht]

theorem valid_length (u : List Nat) (h : valid u) : u.length=6 := bounded_length _ _ h.1

theorem capture_no_promoted (u : List Nat) (hu : valid u) : ∀ r ∈ capture u, r ≠ (13 : Fin 14) := by
  intro r hr
  obtain ⟨n,hn,rfl⟩ := List.mem_map.mp hr
  have hb := bounded_entries _ _ hu.1 n hn
  intro he
  have hv := congrArg Fin.val he
  simp only [Fin.ofNat,Nat.mod_eq_of_lt (show n < 14 by omega)] at hv
  omega

theorem eligible_zero (u : List Nat) (hu : valid u) (i : Fin 6) (hi : eligible u i) :
    u[i.val]? = some 0 := by
  have hl : (capture u).length=6 := by simpa [capture] using valid_length u hu
  have ho := eligible_origin_absent _ _ _ hi
  rw [uFile_at _ hl i] at ho
  have hp := congrArg (fun vs : List Nat => vs[i.val]?) (capture_projection u hu)
  rw [List.getElem?_map,List.getElem?_eq_getElem (show i.val < (capture u).length by omega)] at hp
  simpa only [Option.map_some,ho] using hp.symm

theorem mark_properties (u : List Nat) (hu : valid u) (i : Fin 6) (hi : eligible u i) :
    (mark u i).map shown = u ∧ (mark u i)[i.val]? = some (13 : Fin 14) ∧
      ∀ k : Fin 6, k ≠ i → (mark u i)[k.val]? ≠ some (13 : Fin 14) := by
  have hl : (capture u).length=6 := by simpa [capture] using valid_length u hu
  obtain ⟨hiu,hzero⟩ := List.getElem?_eq_some_iff.mp (eligible_zero u hu i hi)
  constructor
  · rw [mark,List.map_set,capture_projection u hu]
    change u.set i.val 0 = u
    rw [← hzero]
    exact List.set_getElem_self hiu
  · constructor
    · exact List.getElem?_set_self (by omega)
    · intro k hki hp
      have hk : i.val ≠ k.val := by intro he; exact hki (Fin.ext he.symm)
      rw [mark,List.getElem?_set,ite_eq_right hk] at hp
      obtain ⟨hlen,he⟩ := List.getElem?_eq_some_iff.mp hp
      exact capture_no_promoted u hu _ (List.getElem_mem hlen) he

/-- Exactly one promoted slot, with every other absent slot captured. This is
the singleton set queried by the original provider, not an origin assignment. -/
def Singleton (u : List Nat) (i : Fin 6) : Prop :=
  ∃ st, R st ∧ st.map shown=u ∧ st[i.val]?=some (13 : Fin 14) ∧
    ∀ k : Fin 6, k ≠ i → st[k.val]? ≠ some (13 : Fin 14)

theorem singleton_iff (u : List Nat) (i : Fin 6) : Singleton u i ↔ valid u ∧ eligible u i := by
  constructor
  · rintro ⟨st,hr,hp,hi,_⟩
    have hu := (projected_iff u).mp ⟨st,hr,hp⟩
    have he := marked_eligible st (reach_classified st hr) i hi
    have huf := uFile_projection st (capture u) (hp.trans (capture_projection u hu).symm)
    exact ⟨hu,by simpa only [eligible,huf] using he⟩
  · rintro ⟨hu,hi⟩
    obtain ⟨hp,hself,hother⟩ := mark_properties u hu i hi
    exact ⟨mark u i,singleton_reachable u hu i hi,hp,hself,hother⟩

theorem projected_coverage (u : List Nat) :
    (∃ st, R st ∧ st.map shown=u) ↔ OrderedFile.Admissible OrderedFile.lanceSlots u :=
  projected_iff u

theorem projection_values (ls : List Slot) (st : State) (c : Colour) (k : Kind) :
    (((ls.zip st).filter fun (s,_) => decide (s=(c,k))).map fun (_,r) => shown r) =
      (((ls.zip (st.map shown)).filter fun (s,_) => decide (s=(c,k))).map Prod.snd) := by
  induction ls generalizing st with
  | nil => simp
  | cons s ls ih =>
    cases st with
    | nil => simp
    | cons r st =>
      by_cases hs : s=(c,k)
      · simp [hs,ih st]
      · simp [hs,ih st]

theorem concrete_u (u : List Nat) (hu : valid u) (x : Fin 12) (hx : x.val=0 ∨ x.val=11) :
    uFile slots (capture u) = ConcreteDP.localU (x,u) := by
  funext c k
  rw [uFile,projection_values,capture_projection u hu]
  simp only [ConcreteDP.localU,ConcreteDP.labels,hx,ite_eq_left]
  rfl

/-- Exactly the local ranks consumed by both actual lance-file enumerators. -/
theorem concrete_enumeration (u : List Nat) (x : Fin 12) (hx : x.val=0 ∨ x.val=11) :
    (x,u) ∈ ConcreteDP.localConfigs x ↔ ∃ st, R st ∧ st.map shown=u := by
  rw [ConcreteDP.localConfigs_iff,projected_iff]
  simp only [ConcreteDP.LocalAdmissible,ConcreteDP.labels,hx,ite_eq_left,true_and]
  rfl

/-- Exactly the singleton queries used for eligibility capacities. Alternative
promotion origins are not additional canonical configurations. -/
theorem concrete_singleton (u : List Nat) (hu : valid u) (x : Fin 12)
    (hx : x.val=0 ∨ x.val=11) (i : Fin 6) :
    Singleton u i ↔ Eligible (ConcreteDP.localU (x,u)) (label i).1 (label i).2 := by
  rw [singleton_iff,eligible,concrete_u u hu x hx]
  exact and_iff_right hu


end ChuShogi.LanceProvider
