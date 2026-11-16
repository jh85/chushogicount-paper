import ChuShogi.GroupCapacity
import ChuShogi.PromotedCoordinates
import ChuShogi.PromotedEGF

/-! Disjoint-type special polynomial factorization after each overlapping pair
of files is aggregated. The pawn polynomial still uses the whole joint bound.
-/
namespace ChuShogi.SpecialPolynomials
open Specification Promotion ConcreteDP SummaryBridge GroupCapacity GroupedFiles
open EGFConvolution CoefficientEquivalence

def joined (p g l : Summary) : Summary := add (add p g) l
def lanceTables (s : Summary) : List Table :=
  [PromotedCoordinates.typeTable s.bL,PromotedCoordinates.typeTable s.wL,
   PromotedCoordinates.typeTable s.bRC,PromotedCoordinates.typeTable s.wRC]
def goBetweenTables (s : Summary) : List Table :=
  [PromotedCoordinates.typeTable s.bGB,PromotedCoordinates.typeTable s.wGB]

theorem cap_join (p g l : Summary)
    (hp : ZeroFor (fun k => k ≠ .pawn) p)
    (hg : ZeroFor (fun k => k = .lance ∨ k = .chariot) g)
    (hl : ZeroFor (fun k => k = .goBetween) l) (c : Colour) (k : Kind) (hk : k ≠ .pawn) :
    cap (joined p g l) c k = if k = .goBetween then cap g c k else cap l c k := by
  simp only [joined,cap_add,hp c k hk,Nat.zero_add]
  by_cases h : k = .goBetween
  · rw [hl c k h,ite_eq_left h,Nat.add_zero]
  · have hk' : k = .lance ∨ k = .chariot := by cases k <;> simp_all
    rw [hg c k hk',ite_eq_right h,Nat.zero_add]

theorem tables_split (p g l : Summary)
    (hp : ZeroFor (fun k => k ≠ .pawn) p)
    (hg : ZeroFor (fun k => k = .lance ∨ k = .chariot) g)
    (hl : ZeroFor (fun k => k = .goBetween) l) :
    PromotedCoordinates.tables (joined p g l) =
      PromotedCoordinates.pawnTable (joined p g l) :: (lanceTables l ++ goBetweenTables g) := by
  have hL (c : Colour) : cap (joined p g l) c .lance = cap l c .lance := by
    simpa using cap_join p g l hp hg hl c .lance (by decide)
  have hRC (c : Colour) : cap (joined p g l) c .chariot = cap l c .chariot := by
    simpa using cap_join p g l hp hg hl c .chariot (by decide)
  have hGB (c : Colour) : cap (joined p g l) c .goBetween = cap g c .goBetween := by
    simpa using cap_join p g l hp hg hl c .goBetween (by decide)
  change [_,PromotedCoordinates.typeTable (cap (joined p g l) .black .lance),
    PromotedCoordinates.typeTable (cap (joined p g l) .white .lance),
    PromotedCoordinates.typeTable (cap (joined p g l) .black .chariot),
    PromotedCoordinates.typeTable (cap (joined p g l) .white .chariot),
    PromotedCoordinates.typeTable (cap (joined p g l) .black .goBetween),
    PromotedCoordinates.typeTable (cap (joined p g l) .white .goBetween)] = _
  rw [hL,hL,hRC,hRC,hGB,hGB]
  rfl

theorem coefficients_split (p g l : Summary)
    (hp : ZeroFor (fun k => k ≠ .pawn) p)
    (hg : ZeroFor (fun k => k = .lance ∨ k = .chariot) g)
    (hl : ZeroFor (fun k => k = .goBetween) l) :
    Equivalent (PromotedCoordinates.coefficients (joined p g l))
      (convolve (PromotedCoordinates.pawnTable (joined p g l))
        (convolve (product (lanceTables l)) (product (goBetweenTables g)))) := by
  intro f
  unfold PromotedCoordinates.coefficients
  rw [tables_split p g l hp hg hl]
  change integral (convolve _ (product (lanceTables l++goBetweenTables g))) f = _
  exact convolve_congr _ _ _ _ (fun _ => rfl) (product_append _ _) f

theorem actual_coefficients_split (pe ge le : Summary × Nat) (hp : pe ∈ plainTable)
    (hg : ge ∈ goBetweenTable) (hl : le ∈ lanceTable) :
    Equivalent (PromotedCoordinates.coefficients (joined pe.1 ge.1 le.1))
      (convolve (PromotedCoordinates.pawnTable (joined pe.1 ge.1 le.1))
        (convolve (product (lanceTables le.1)) (product (goBetweenTables ge.1)))) :=
  coefficients_split _ _ _ (plain_support pe hp) (goBetween_support ge hg) (lance_support le hl)

def slotCount (c : Colour) (k : Kind) : Nat := (indices.flatMap labels).count (c,k)

theorem slotCount_nonpawn (c : Colour) (k : Kind) (hk : k ≠ .pawn) : slotCount c k = 2 := by
  cases c <;> cases k <;> first | contradiction | decide

theorem lance_division_exact (e : Summary × Nat) (he : e ∈ lanceTable)
    (c : Colour) (k : Kind) (i : Nat) (hi : i ≤ cap e.1 c k) :
    ((((2 : Nat).factorial)/i.factorial : Nat) : ℚ) =
      ((2 : Nat).factorial : ℚ)*(1/(i.factorial : ℚ)) :=
  PromotedEGF.special_coefficient_exact 2 _ i hi (lance_cap_bound c k e he)

theorem goBetween_division_exact (e : Summary × Nat) (he : e ∈ goBetweenTable)
    (c : Colour) (k : Kind) (i : Nat) (hi : i ≤ cap e.1 c k) :
    ((((2 : Nat).factorial)/i.factorial : Nat) : ℚ) =
      ((2 : Nat).factorial : ℚ)*(1/(i.factorial : ℚ)) :=
  PromotedEGF.special_coefficient_exact 2 _ i hi (goBetween_cap_bound c k e he)

end ChuShogi.SpecialPolynomials
