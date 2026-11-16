import ChuShogi.EGFConvolution

/-! The source-style free group coefficient calculation, with canonical royal
and jumper states and distinct bishop/kirin square restrictions. Coefficients
are rational. Equal coefficient keys may have several canonical contributions.
-/
namespace ChuShogi.FreeEGF
open Specification Promotion CanonicalGroups GroupCoverage EGFConvolution EGFArithmetic

structure Input where
  degree : Degree
  divisor : Nat
  deriving DecidableEq, Repr

def term (i : Input) : Term := (i.degree,1/(i.divisor : ℚ))

def stdInputs : List Input := (stdStates 2).map fun (u,p) =>
  ⟨⟨u+p,0,0⟩,u.factorial*p.factorial⟩

def royalInputs (r : Bool) (c : Colour) : List Input :=
  (royalList r c).map fun (k,e) => ⟨⟨k+e,0,0⟩,k.factorial⟩

def bishopInputs : List Input := bishopStates.map fun (u0,u1,p) =>
  ⟨⟨p,u0,u1⟩,u0.factorial*u1.factorial*p.factorial⟩

def kirinInputs : List Input := jumperStates.map fun (small,big) =>
  ⟨⟨big,0,small⟩,big.factorial⟩

def phoenixInputs : List Input := jumperStates.map fun (small,big) =>
  ⟨⟨small+big,0,0⟩,big.factorial⟩

def sideInputs (r : Bool) (c : Colour) : List (List Input) :=
  royalInputs r c :: ordinary.map (fun _ => stdInputs) ++ [bishopInputs,kirinInputs,phoenixInputs]

def inputs (r : Bool) : List (List Input) := sideInputs r .black ++ sideInputs r .white

def tables (r : Bool) : List Table := (inputs r).map (List.map term)

/-- A finite convolution, with no classical choice or symbolic Board universe
in its execution path. -/
def coefficients (r : Bool) : Table := product (tables r)

def ValidInput (i : Input) : Prop := i.divisor ≠ 0 ∧ i.divisor ∣ i.degree.m.factorial

instance (i : Input) : Decidable (ValidInput i) := inferInstanceAs
  (Decidable (i.divisor ≠ 0 ∧ i.divisor ∣ i.degree.m.factorial))

theorem inputs_valid (r : Bool) : ∀ xs ∈ inputs r, ∀ i ∈ xs, ValidInput i := by
  cases r <;> decide

theorem term_integral (i : Input) (h : ValidInput i) : Labelled (term i) := by
  refine ⟨i.degree.m.factorial/i.divisor,?_⟩
  have hc := cast_exact_div i.degree.m.factorial i.divisor h.1 h.2
  change (1/(i.divisor : ℚ))*(i.degree.m.factorial : ℚ) = _
  rw [hc]
  ring

/-- This justifies `_free_polys`' integer conversion after multiplying the
degree-m coefficient by m!. No claim of intermediate EGF integrality is made. -/
theorem coefficients_integral (r : Bool) : IntegralTable (coefficients r) := by
  apply product_integral
  intro t ht
  obtain ⟨xs,hxs,rfl⟩ := List.mem_map.mp ht
  intro e he
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp he
  exact term_integral i (inputs_valid r xs hxs i hi)

theorem coefficients_expansion (r : Bool) (f : Degree → ℚ) :
    integral (coefficients r) f =
      ((WeightedDP.tuples (tables r)).map fun es => tupleWeight es*f (tupleDegree es)).sum :=
  product_expansion (tables r) f

def labelledCoefficients (r : Bool) : List (Degree × Nat) :=
  (coefficients r).map fun (d,w) => (d,(w*(d.m.factorial : ℚ)).num.toNat)

theorem labelled_conversion (r : Bool) (e : Term) (he : e ∈ coefficients r) :
    (((e.2*(e.1.m.factorial : ℚ)).num.toNat : Nat) : ℚ) = e.2*(e.1.m.factorial : ℚ) := by
  obtain ⟨n,hn⟩ := coefficients_integral r e he
  rw [hn]
  simp

end ChuShogi.FreeEGF
