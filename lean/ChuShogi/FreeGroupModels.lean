import ChuShogi.FiniteCoefficientModel
import ChuShogi.CoefficientEquivalence

/-! Complete coefficient models of the actual canonical free group choices.
These are proof adapters to the executable tables in `FreeEGF`; no term-image
injectivity is assumed. Different canonical states with equal terms still add.
-/
namespace ChuShogi.FreeGroupModels
open Specification Promotion CanonicalGroups GroupCoverage FreeEGF EGFConvolution
open FiniteCoefficientModel

def stdInput (v : Nat × Nat) : Input := ⟨⟨v.1+v.2,0,0⟩,v.1.factorial*v.2.factorial⟩
def royalInput (v : Nat × Nat) : Input := ⟨⟨v.1+v.2,0,0⟩,v.1.factorial⟩
def bishopInput (v : Nat × Nat × Nat) : Input := ⟨⟨v.2.2,v.1,v.2.1⟩,v.1.factorial*v.2.1.factorial*v.2.2.factorial⟩
def kirinInput (v : Nat × Nat) : Input := ⟨⟨v.2,0,v.1⟩,v.2.factorial⟩
def phoenixInput (v : Nat × Nat) : Input := ⟨⟨v.1+v.2,0,0⟩,v.2.factorial⟩

noncomputable def inputModel {A : Type} [DecidableEq A] (xs : List A) (hn : xs.Nodup)
    (i : A → Input) : Model {a : A // a ∈ xs} :=
  members xs hn (fun a => (i a).degree) (fun a => 1/((i a).divisor : ℚ))

theorem inputModel_table {A : Type} [DecidableEq A] (xs : List A) (hn : xs.Nodup)
    (i : A → Input) : (inputModel xs hn i).table = (xs.map i).map term := by
  rw [inputModel,members_table]
  simp only [List.map_map]
  rfl

noncomputable def std := inputModel (stdStates 2) (stdStates_nodup 2) stdInput
noncomputable def royal (r : Bool) (c : Colour) := inputModel (royalList r c) (royalList_nodup r c) royalInput
noncomputable def bishop := inputModel bishopStates bishopStates_nodup bishopInput
noncomputable def kirin := inputModel jumperStates jumperStates_nodup kirinInput
noncomputable def phoenix := inputModel jumperStates jumperStates_nodup phoenixInput

theorem std_table : std.table = stdInputs.map term := by rw [std,inputModel_table]; rfl
theorem royal_table (r : Bool) (c : Colour) : (royal r c).table = (royalInputs r c).map term := by
  rw [royal,inputModel_table]; rfl
theorem bishop_table : bishop.table = bishopInputs.map term := by rw [bishop,inputModel_table]; rfl
theorem kirin_table : kirin.table = kirinInputs.map term := by rw [kirin,inputModel_table]; rfl
theorem phoenix_table : phoenix.table = phoenixInputs.map term := by rw [phoenix,inputModel_table]; rfl

abbrev SideData (r : Bool) (c : Colour) :=
  GroupConfigurations.Member (royalList r c) ×
    ((Fin 10 → GroupConfigurations.Member (stdStates 2)) ×
      (GroupConfigurations.Member bishopStates ×
        (GroupConfigurations.Member jumperStates × GroupConfigurations.Member jumperStates)))

noncomputable def side (r : Bool) (c : Colour) : Model (SideData r c) :=
  FiniteCoefficientModel.product (royal r c)
    (FiniteCoefficientModel.product (power std 10)
      (FiniteCoefficientModel.product bishop (FiniteCoefficientModel.product kirin phoenix)))

abbrev Data (r : Bool) := SideData r .black × SideData r .white

noncomputable def model (r : Bool) : Model (Data r) :=
  FiniteCoefficientModel.product (side r .black) (side r .white)

theorem side_tables (r : Bool) (c : Colour) : (sideInputs r c).map (List.map term) =
    (royalInputs r c).map term :: List.replicate 10 (stdInputs.map term) ++
      [bishopInputs.map term,kirinInputs.map term,phoenixInputs.map term] := rfl

theorem side_equivalent (r : Bool) (c : Colour) : CoefficientEquivalence.Equivalent (side r c).table
    (EGFConvolution.product ((sideInputs r c).map (List.map term))) := by
  intro f
  dsimp only [side,FiniteCoefficientModel.product]
  rw [power_table,std_table,royal_table,bishop_table,kirin_table,phoenix_table,side_tables]
  simp only [List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,EGFConvolution.product]
  simp_rw [integral_convolve]
  simp only [CoefficientEquivalence.integral_unit,CoefficientEquivalence.degree_add_zero,
    CoefficientEquivalence.degree_zero_add,CoefficientEquivalence.degree_add_assoc]

/-- Complete refinement of executable free coefficients to all canonical raw
group-coordinate choices, with their exact reciprocal factorial weights. -/
theorem coefficients_model (r : Bool) (f : Degree → ℚ) :
    integral (coefficients r) f = ∑ q : Data r, (model r).weight q*f ((model r).key q) := by
  have hp := CoefficientEquivalence.product_append
    ((sideInputs r .black).map (List.map term)) ((sideInputs r .white).map (List.map term))
  have he := CoefficientEquivalence.convolve_congr _ _ _ _
    (fun f => (side_equivalent r .black f).symm) (fun f => (side_equivalent r .white f).symm)
  change integral (EGFConvolution.product (tables r)) f = _
  rw [tables,inputs,List.map_append,hp f,he f]
  exact (model r).correct f

end ChuShogi.FreeGroupModels
