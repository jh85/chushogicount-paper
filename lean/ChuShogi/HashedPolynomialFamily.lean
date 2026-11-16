import ChuShogi.PolynomialFamily
import ChuShogi.RationalCoefficientHash

/-! Executable hashed family coefficients, extensionally equal to the checked
reference family table. The symbolic family universe remains unenumerated. -/
namespace ChuShogi.HashedPolynomialFamily
open EGFConvolution CoefficientEquivalence PolynomialFamily

def table {A : Type} : Family A → Table
  | .leaf a k w => a.values.map fun x => (k x,w x)
  | .product x y => RationalCoefficientHash.convolve (table x) (table y)
  | .relabel f _ => table f

theorem equivalent {A : Type} (f : Family A) : Equivalent (table f) (PolynomialFamily.table f) := by
  induction f with
  | leaf _ _ _ => intro _; rfl
  | product x y ix iy =>
    intro test
    exact (RationalCoefficientHash.equivalent (table x) (table y) test).trans
      (convolve_congr _ _ _ _ ix iy test)
  | relabel f _ ih => exact ih

end ChuShogi.HashedPolynomialFamily
