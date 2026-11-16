import ChuShogi.ScaledPolynomials

/-! The reduced state retains joint pawn capacity, occupied squares of both
classes, and total promoted non-pawn degree. Type capacities have been integrated
by the special polynomials; the following identities justify that erasure.
-/
namespace ChuShogi.ReducedGeometry
open Specification Promotion ConcreteDP GroupCapacity GroupedFiles SpecialPolynomials
open EGFConvolution CoefficientEquivalence

def key (s : Summary) (k : Nat) : List Nat := [s.joint,s.d0,s.d1,k]
def merge (a b : List Nat) : List Nat :=
  [a[0]?.getD 0+b[0]?.getD 0,a[1]?.getD 0+b[1]?.getD 0,
   a[2]?.getD 0+b[2]?.getD 0,a[3]?.getD 0+b[3]?.getD 0]

theorem merge_key (s t : Summary) (a b : Nat) : merge (key s a) (key t b) = key (ConcreteDP.add s t) (a+b) := rfl

def pawnSummary (j : Nat) : Summary := { ConcreteDP.zero with cb := j,cw := j,joint := j }

theorem pawn_table_shape (s : Summary) (h : PawnShape s) :
    PromotedCoordinates.pawnTable s = PromotedCoordinates.pawnTable (pawnSummary s.joint) := by
  unfold PromotedCoordinates.pawnTable PromotedCoordinates.pawnStates
  rw [h.1,h.2]
  rfl

def finishDegree (r : Bool) (s : Summary) (nonpawn : Degree) : ℚ :=
  integral (convolve (FreeEGF.coefficients r) (PromotedCoordinates.pawnTable (pawnSummary s.joint)))
    (fun free => CompletionCoefficients.placement (72-s.d0) (72-s.d1) (EGFConvolution.add free nonpawn))

def finish (r : Bool) (xs : List Nat) : ℚ :=
  let j := xs[0]?.getD 0
  let d0 := xs[1]?.getD 0
  let d1 := xs[2]?.getD 0
  let k := xs[3]?.getD 0
  integral (convolve (FreeEGF.coefficients r) (PromotedCoordinates.pawnTable (pawnSummary j)))
    (fun free => CompletionCoefficients.placement (72-d0) (72-d1)
      (EGFConvolution.add free (ScaledPolynomials.lift k)))

theorem finish_key (r : Bool) (s : Summary) (k : Nat) :
    finish r (key s k) = finishDegree r s (ScaledPolynomials.lift k) := rfl

theorem evaluate_special (r : Bool) (p g l : Summary)
    (hp : ZeroFor (fun k => k ≠ .pawn) p)
    (hg : ZeroFor (fun k => k = .lance ∨ k = .chariot) g)
    (hl : ZeroFor (fun k => k = .goBetween) l) (hs : PawnShape (joined p g l)) :
    CompletionCoefficients.evaluate r (joined p g l) =
      integral (product (goBetweenTables g)) (fun dg =>
        integral (product (lanceTables l)) (fun dl => finishDegree r (joined p g l) (EGFConvolution.add dg dl))) := by
  let F := FreeEGF.coefficients r
  let P := PromotedCoordinates.pawnTable (pawnSummary (joined p g l).joint)
  let L := product (lanceTables l)
  let G := product (goBetweenTables g)
  let t := CompletionCoefficients.placement (72-(joined p g l).d0) (72-(joined p g l).d1)
  have he : Equivalent (PromotedCoordinates.coefficients (joined p g l)) (convolve P (convolve L G)) := by
    simpa only [pawn_table_shape _ hs] using coefficients_split p g l hp hg hl
  calc
    CompletionCoefficients.evaluate r (joined p g l) = integral (convolve F (convolve P (convolve L G))) t :=
      convolve_congr _ _ _ _ (fun _ => rfl) he t
    _ = integral (convolve (convolve F P) (convolve L G)) t := (convolve_assoc _ _ _ t).symm
    _ = integral (convolve (convolve L G) (convolve F P)) t := convolve_comm _ _ t
    _ = integral (convolve L G) (fun d => integral (convolve F P) (fun e => t (EGFConvolution.add d e))) :=
      integral_convolve _ _ t
    _ = integral (convolve L G) (fun d => finishDegree r (joined p g l) d) := by
      apply congrArg (integral (convolve L G))
      funext d
      apply congrArg (integral (convolve F P))
      funext e
      rw [degree_add_comm]
    _ = integral (convolve G L) (fun d => finishDegree r (joined p g l) d) := convolve_comm _ _ _
    _ = _ := integral_convolve _ _ _

theorem actual_scaled (r : Bool) (pe ge le : Summary × Nat)
    (hp : pe ∈ plainTable) (hg : ge ∈ goBetweenTable) (hl : le ∈ lanceTable) :
    RationalTable.integral (ScaledPolynomials.goBetween ge.1) (fun kg =>
      RationalTable.integral (ScaledPolynomials.lance le.1) (fun kl =>
        finish r (key (joined pe.1 ge.1 le.1) (kg+kl)))) =
      64*CompletionCoefficients.evaluate r (joined pe.1 ge.1 le.1) := by
  let s := joined pe.1 ge.1 le.1
  have hs : PawnShape s := pawn_shape_add _ _
    (pawn_shape_add _ _ (table_pawn_shape plainFiles pe hp) (table_pawn_shape goBetweenFiles ge hg))
    (table_pawn_shape lanceFiles le hl)
  have hL (kg : Nat) : RationalTable.integral (ScaledPolynomials.lance le.1)
      (fun kl => finish r (key s (kg+kl))) =
        16*integral (product (lanceTables le.1))
          (fun dl => finishDegree r s (EGFConvolution.add (ScaledPolynomials.lift kg) dl)) := by
    simpa only [finish_key,ScaledPolynomials.lift_add] using ScaledPolynomials.lance_integral le hl
      (fun dl => finishDegree r s (EGFConvolution.add (ScaledPolynomials.lift kg) dl))
  change RationalTable.integral (ScaledPolynomials.goBetween ge.1)
    (fun kg => RationalTable.integral (ScaledPolynomials.lance le.1) (fun kl => finish r (key s (kg+kl)))) = _
  simp_rw [hL]
  rw [RationalTable.integral_mul]
  rw [ScaledPolynomials.goBetween_integral ge hg
    (fun dg => integral (product (lanceTables le.1)) (fun dl => finishDegree r s (EGFConvolution.add dg dl)))]
  rw [evaluate_special r _ _ _ (plain_support pe hp) (goBetween_support ge hg) (lance_support le hl) hs]
  ring

end ChuShogi.ReducedGeometry
