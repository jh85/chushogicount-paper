import ChuShogi.CompressedPolynomialSelection
open ChuShogi PolynomialFamily PolynomialSelectionWeights EGFConvolution
def alphabet (n : Nat) : Alphabet (Fin n) :=
  ⟨inferInstance,List.finRange n,List.nodup_finRange n,List.mem_finRange⟩
def first : Family (Fin 2) := .leaf (alphabet 2) (fun _ => zero) (fun _ => 1/2)
def second : Family (Fin 3) := .leaf (alphabet 3) (fun _ => zero) (fun _ => 1/3)
def choices : Family (Fin 2 × Fin 3) := .product first second
def test : Degree → ℚ := fun _ => 6
theorem natural : NaturalWeights choices test := by
  intro a
  refine ⟨1,?_⟩
  norm_num [choices,first,second,weight,test]
theorem six : total choices test=6 := by
  change (integral (convolve (table first) (table second)) test).num.toNat=6
  rw [integral_convolve]
  norm_num [first,second,table,integral,alphabet,test]
#eval (List.finRange 6).map fun i =>
  let x := CompressedPolynomialSelection.unrank choices test natural (Fin.cast six.symm i)
  (x.1.1.val,x.1.2.val,x.2.val)
#print axioms natural
#print axioms six
