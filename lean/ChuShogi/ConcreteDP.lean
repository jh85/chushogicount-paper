import ChuShogi.Specification
import ChuShogi.WeightedDP

/-!
Concrete file aggregation for the declarative I1--I9 counter. The summary is
Python's full feature vector, before the optional suppression of pawn statistics
and special-type polynomial grouping. No file-game reachability hypothesis is
needed: those belong to correspondence with the source's table provider.
-/
namespace ChuShogi.ConcreteDP
open Promotion Specification

abbrev Label := Colour × Kind

def labels (x : Fin 12) : List Label :=
  if x.val = 0 ∨ x.val = 11 then
    [(.black,.lance), (.black,.chariot), (.black,.pawn),
     (.white,.pawn), (.white,.chariot), (.white,.lance)]
  else if x.val = 3 ∨ x.val = 8 then
    [(.black,.pawn), (.black,.goBetween), (.white,.goBetween), (.white,.pawn)]
  else [(.black,.pawn), (.white,.pawn)]

def orderedLabel : Label → OrderedFile.Slot
  | (.black,.pawn) => .blackPawn
  | (.white,.pawn) => .whitePawn
  | _ => .other

def rawConfigs (x : Fin 12) : List (List Nat) :=
  OrderedFile.enumerate 0 ((labels x).map orderedLabel)

abbrev Local := Fin 12 × List Nat

def LocalAdmissible (x : Fin 12) (u : Local) : Prop :=
  u.1 = x ∧ OrderedFile.Admissible ((labels x).map orderedLabel) u.2

def localConfigs (x : Fin 12) : List Local := (rawConfigs x).map (x, ·)

theorem localConfigs_iff (x : Fin 12) (u : Local) :
    u ∈ localConfigs x ↔ LocalAdmissible x u := by
  rcases u with ⟨y,rs⟩
  simp only [localConfigs, List.mem_map, Prod.mk.injEq, LocalAdmissible]
  constructor
  · rintro ⟨r,hr,hxy,rfl⟩
    exact ⟨hxy.symm, (OrderedFile.exact_enumeration _).2 _ |>.mp hr⟩
  · rintro ⟨rfl,hr⟩
    exact ⟨rs,(OrderedFile.exact_enumeration _).2 _ |>.mpr hr,rfl,rfl⟩

theorem localConfigs_nodup (x : Fin 12) : (localConfigs x).Nodup := by
  rw [localConfigs, List.nodup_iff_pairwise_ne, List.pairwise_map]
  apply List.Pairwise.imp _ (OrderedFile.enumerate_nodup _ _)
  intro a b hab heq
  exact hab (Prod.mk.inj heq).2

/-- The slot lookup used by declarative eligibility. -/
def localU (u : Local) : UFile := fun c k =>
  ((((labels u.1).zip u.2).filter fun (label,_) => decide (label = (c,k))).map Prod.snd).sum

/-- Optional statistics, joint pawn capacities, class occupancy, six capacities. -/
structure Summary where
  uPB : Nat
  uPW : Nat
  cb : Nat
  cw : Nat
  joint : Nat
  d0 : Nat
  d1 : Nat
  bL : Nat
  wL : Nat
  bRC : Nat
  wRC : Nat
  bGB : Nat
  wGB : Nat
  deriving DecidableEq, Repr

def zero : Summary := ⟨0,0,0,0,0,0,0,0,0,0,0,0,0⟩

def add (s t : Summary) : Summary :=
  ⟨s.uPB+t.uPB,s.uPW+t.uPW,s.cb+t.cb,s.cw+t.cw,s.joint+t.joint,
   s.d0+t.d0,s.d1+t.d1,s.bL+t.bL,s.wL+t.wL,s.bRC+t.bRC,s.wRC+t.wRC,
   s.bGB+t.bGB,s.wGB+t.wGB⟩

def occupied (u : Local) (a : Nat) : Nat :=
  (u.2.filter fun r => decide (r ≠ 0 ∧ (u.1.val + r) % 2 = a)).length

def bit (p : Prop) [Decidable p] : Nat := if p then 1 else 0

def localCap (u : Local) (c : Colour) (k : Kind) : Nat :=
  bit (HasSlot u.1 c k ∧ Eligible (localU u) c k)

def feature (u : Local) : Summary :=
  let pawn := bit (localU u .black .pawn = 0 ∧ localU u .white .pawn = 0)
  ⟨bit (localU u .black .pawn ≠ 0),bit (localU u .white .pawn ≠ 0),
   pawn,pawn,pawn,occupied u 0,occupied u 1,
   localCap u .black .lance,localCap u .white .lance,
   localCap u .black .chariot,localCap u .white .chariot,
   localCap u .black .goBetween,localCap u .white .goBetween⟩

def indices : List (Fin 12) := (List.finRange 12).reverse

def files : List (List Local) := indices.map localConfigs

def admissible : List (Local → Prop) := indices.map LocalAdmissible

def Valid (u : List Local) : Prop := WeightedDP.Valid admissible u

def summary (u : List Local) : Summary := WeightedDP.summary zero add feature u

def table : WeightedDP.Table Summary := WeightedDP.dp zero add feature files

theorem enumerates (xs : List (Fin 12)) :
    WeightedDP.Enumerates (xs.map LocalAdmissible) (xs.map localConfigs) := by
  induction xs with
  | nil => trivial
  | cons x xs ih => exact ⟨localConfigs_iff x,ih⟩

theorem files_nodup : ∀ xs ∈ files, xs.Nodup := by
  intro xs hx
  rcases List.mem_map.mp hx with ⟨x,_,rfl⟩
  exact localConfigs_nodup x

/-- All application-specific local-enumeration hypotheses are discharged. -/
theorem concrete_dp_fibre (s : Summary) :
    let fibre := (WeightedDP.tuples files).filter fun u => decide (summary u = s)
    fibre.Nodup ∧ (∀ u, u ∈ fibre ↔ Valid u ∧ summary u = s) ∧
      WeightedDP.lookup table s = fibre.length :=
  WeightedDP.dp_fibre zero add feature admissible files (enumerates indices) files_nodup s

/-- Exact weighted aggregation for any supplied completion function. It remains
necessary to prove that the concrete completion function counts Candidate Boards. -/
theorem concrete_dp_integral (completion : Summary → Nat) :
    WeightedDP.integral table completion =
      ((WeightedDP.tuples files).map fun u => completion (summary u)).sum :=
  WeightedDP.dp_integral zero add feature files completion

/-- Full setup: the two pawn capacities and joint capacity coincide file by file. -/
theorem pawn_capacities (u : Local) :
    (feature u).cb = localCap u .black .pawn ∧
    (feature u).cw = localCap u .white .pawn ∧
    (feature u).joint = (feature u).cb := by
  simp only [feature, localCap, HasSlot, true_and, pawn_eligibility]

end ChuShogi.ConcreteDP
