import ChuShogi.CanonicalAlphabet

/-! Symbolic finiteness of canonical configurations. This encoding is used for
sum/bijection proofs only; efficient evaluation must use coefficient convolution.
-/
namespace ChuShogi.FiniteConfigurations
open Specification Promotion CompletionProfiles ConcreteDP GroupCoverage GroupConfigurations CanonicalAlphabet

noncomputable instance roleFintype : Fintype Role :=
  Fintype.ofInjective (fun p : Role => (Colour.black,p)) (fun _ _ h => (Prod.mk.inj h).2)

theorem material_bound (n : Counts) (h : Material n) (c : Colour) (p : Role) : n c p ≤ 12 := by
  have hs (k : Separate) : n c (.native k.base) ≤ 12 ∧ n c (.promoted k) ≤ 12 := by
    have hh := (h c).1 k
    have hn : initialSeparate k ≤ 12 := by cases k <;> decide
    omega
  cases p with
  | promoted k => exact (hs k).2
  | native b =>
    cases b with
    | pawn => exact (hs .pawn).1
    | lance => exact (hs .lance).1
    | chariot => exact (hs .chariot).1
    | goBetween => exact (hs .goBetween).1
    | gold => exact (hs .gold).1
    | silver => exact (hs .silver).1
    | copper => exact (hs .copper).1
    | leopard => exact (hs .leopard).1
    | tiger => exact (hs .tiger).1
    | sideMover => exact (hs .sideMover).1
    | verticalMover => exact (hs .verticalMover).1
    | rook => exact (hs .rook).1
    | dragonHorse => exact (hs .dragonHorse).1
    | dragonKing => exact (hs .dragonKing).1
    | bishop => exact (hs .bishop).1
    | elephant => have hh := (h c).2.1; omega
    | king => have hh := (h c).2.2.1; omega
    | kirin => have hh := (h c).2.2.2.1; omega
    | lion => have hh := (h c).2.2.2.2.1; omega
    | phoenix => have hh := (h c).2.2.2.2.2.1; omega
    | freeKing => have hh := (h c).2.2.2.2.2.2; omega

theorem class_bounds (s : Summary) (hs : Sized s) (g : Config r s) (c : Colour) (p : Role) :
    class0 g c p < 13 ∧ class1 g c p < 13 := by
  have hv := (grouped_iff r s hs _ _).mp (grouped_classes g)
  rcases hv with ⟨_,⟨_,_,_,_,_,hm⟩,_⟩
  rw [total_classes] at hm
  have hb := material_bound _ hm c p
  have he := congrFun (congrFun (total_classes g) c) p
  change class0 g c p+class1 g c p = counts g c p at he
  omega

def encode (s : Summary) (hs : Sized s) (g : Config r s) :
    (Colour → Role → Fin 13) × (Colour → Role → Fin 13) :=
  (fun c p => ⟨class0 g c p,(class_bounds s hs g c p).1⟩,
   fun c p => ⟨class1 g c p,(class_bounds s hs g c p).2⟩)

theorem encode_injective (s : Summary) (hs : Sized s) : Function.Injective (encode (r := r) s hs) := by
  intro g h he
  apply canonical_injective
  · funext c p
    exact congrArg Fin.val (congrFun (congrFun (congrArg Prod.fst he) c) p)
  · funext c p
    exact congrArg Fin.val (congrFun (congrFun (congrArg Prod.snd he) c) p)

@[instance_reducible] noncomputable def configFintype (s : Summary) (hs : Sized s) (r : Bool) : Fintype (Config r s) :=
  Fintype.ofInjective (encode s hs) (encode_injective s hs)

end ChuShogi.FiniteConfigurations
