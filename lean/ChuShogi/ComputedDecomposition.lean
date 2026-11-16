import ChuShogi.ComputedRendering

/-! Computable assembly/inverse of the independently proved Board decomposition.
The mathematical rendering is used only to establish equality of functions. -/
namespace ChuShogi.ComputedDecomposition
open Specification StructuralDecomposition

def assemble (p : Parts) : Board := BoardDecomposition.merge (ComputedRendering.tuple p.1) p.2

theorem assemble_eq (r : Bool) (p : Parts) (h : ValidParts r p) : assemble p=StructuralDecomposition.assemble p := by
  rw [assemble,ComputedRendering.tuple_eq p.1 h.1]
  rfl

def equivalence (r : Bool) : {p : Parts // ValidParts r p} ≃ {b : Board // Stratum r b} where
  toFun p := ⟨assemble p.val,by rw [assemble_eq r p.val p.property]; exact assemble_sound r p.val p.property⟩
  invFun b := ⟨decompose b.val,decompose_valid r b.val b.property⟩
  left_inv p := by
    apply Subtype.ext
    change decompose (assemble p.val)=p.val
    rw [assemble_eq r p.val p.property]
    exact decompose_assemble r p.val p.property
  right_inv b := by
    apply Subtype.ext
    change assemble (decompose b.val)=b.val
    rw [assemble_eq r _ (decompose_valid r b.val b.property)]
    exact assemble_decompose r b.val b.property

end ChuShogi.ComputedDecomposition
