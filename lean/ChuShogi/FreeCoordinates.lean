import ChuShogi.FreeGroupModels
import ChuShogi.ConfigurationFactors
import ChuShogi.Indexing

/-! The actual canonical Config free fields and the finite source coefficient
coordinates are bijective, including all twenty ordinary canonical count pairs.
-/
namespace ChuShogi.FreeCoordinates
open Specification Promotion ConcreteDP GroupCoverage GroupConfigurations ConfigurationFactors FreeGroupModels

def ordinaryEquivalence : Fin 10 ≃ {k : Separate // k ∈ ordinary} where
  toFun i := ⟨Indexing.unrank ordinary i,List.getElem_mem i.isLt⟩
  invFun k := Indexing.rank ordinary k.val k.property
  left_inv i := Indexing.rank_unrank ordinary (by decide) i
  right_inv k := Subtype.ext (Indexing.unrank_rank ordinary k.val k.property)

theorem ordinary_value (i : Fin 10) : (ordinaryEquivalence i).val = ordinary[i.val] := rfl

theorem std_ordinary (g : Config r zero) (c : Colour) (i : Fin 10) :
    g.std c (ordinaryEquivalence i).val (ordinaryEquivalence i).property =
      g.std c ordinary[i.val] (List.getElem_mem i.isLt) := rfl

def sideData (g : Config r zero) (c : Colour) : SideData r c :=
  ((g.royal c),(fun i => g.std c (ordinaryEquivalence i).val (ordinaryEquivalence i).property),
    g.bishop c,g.kirin c,g.phoenix c)

def toData (g : Config r zero) : Data r := (sideData g .black,sideData g .white)

def fromData (d : Data r) : Config r zero where
  std c k hk := match c with
    | .black => d.1.2.1 (ordinaryEquivalence.symm ⟨k,hk⟩)
    | .white => d.2.2.1 (ordinaryEquivalence.symm ⟨k,hk⟩)
  royal c := match c with | .black => d.1.1 | .white => d.2.1
  bishop c := match c with | .black => d.1.2.2.1 | .white => d.2.2.2.1
  kirin c := match c with | .black => d.1.2.2.2.1 | .white => d.2.2.2.2.1
  phoenix c := match c with | .black => d.1.2.2.2.2 | .white => d.2.2.2.2.2
  promoted := fun _ _ => 0
  pawn_black := by rfl
  pawn_white := by rfl
  pawn_joint := by rfl
  nonpawn := fun _ _ _ => Nat.zero_le _

theorem from_to (g : Config r zero) : fromData (toData g) = g := by
  apply config_ext
  · funext c k hk
    cases c <;> simp only [fromData,toData,sideData,Equiv.apply_symm_apply]
  · funext c; cases c <;> rfl
  · funext c; cases c <;> rfl
  · funext c; cases c <;> rfl
  · funext c; cases c <;> rfl
  · exact (free_promoted_zero g).symm

theorem to_from (d : Data r) : toData (fromData d) = d := by
  apply Prod.ext
  all_goals
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · funext i
        simp only [toData,sideData,fromData]
        first
        | exact congrArg d.1.2.1 (ordinaryEquivalence.symm_apply_apply i)
        | exact congrArg d.2.2.1 (ordinaryEquivalence.symm_apply_apply i)
      · rfl

def equivalence (r : Bool) : Config r zero ≃ Data r :=
  ⟨toData,fromData,from_to,to_from⟩

/-- The executable `_free_polys` analogue now sums the actual canonical free
configuration type, rather than only a list of possibly repeated term images. -/
theorem coefficients_free_config (r : Bool) (f : EGFConvolution.Degree → ℚ) :
    EGFConvolution.integral (FreeEGF.coefficients r) f =
      ∑ g : Config r zero, (model r).weight (toData g)*f ((model r).key (toData g)) := by
  rw [coefficients_model]
  exact Fintype.sum_equiv (equivalence r).symm _ _ (fun d => by
    change (model r).weight d*f ((model r).key d) =
      (model r).weight (toData (fromData d))*f ((model r).key (toData (fromData d)))
    rw [to_from])

def inputs (g : Config r zero) : List FreeEGF.Input :=
  GroupWeights.configInputs g .black ++ GroupWeights.configInputs g .white

theorem key_inputs (g : Config r zero) : (model r).key (toData g) =
    EGFConvolution.tupleDegree ((inputs g).map FreeEGF.term) := by
  simp [model,side,FiniteCoefficientModel.product,FiniteCoefficientModel.power_key,
    toData,sideData,std,royal,bishop,kirin,phoenix,inputModel,
    FiniteCoefficientModel.members,FiniteCoefficientModel.fromList,
    inputs,GroupWeights.configInputs,
    List.ofFn_succ,std_ordinary,stdInput,royalInput,bishopInput,kirinInput,phoenixInput,
    FreeEGF.term,EGFConvolution.tupleDegree,CoefficientEquivalence.degree_add_zero,
    CoefficientEquivalence.degree_add_assoc]
  simp [ordinary,GroupWeights.stdInput,FreeEGF.term,sep,EGFConvolution.tupleDegree,
    CoefficientEquivalence.degree_add_zero]

theorem weight_inputs (g : Config r zero) : (model r).weight (toData g) =
    EGFConvolution.tupleWeight ((inputs g).map FreeEGF.term) := by
  simp [model,side,FiniteCoefficientModel.product,FiniteCoefficientModel.power_weight,
    toData,sideData,std,royal,bishop,kirin,phoenix,inputModel,
    FiniteCoefficientModel.members,FiniteCoefficientModel.fromList,
    inputs,GroupWeights.configInputs,
    List.ofFn_succ,std_ordinary,stdInput,royalInput,bishopInput,kirinInput,phoenixInput,
    FreeEGF.term,EGFConvolution.tupleWeight,mul_assoc]
  simp [ordinary,GroupWeights.stdInput,FreeEGF.term,sep,EGFConvolution.tupleWeight,mul_assoc]

theorem coefficients_canonical (r : Bool) (f : EGFConvolution.Degree → ℚ) :
    EGFConvolution.integral (FreeEGF.coefficients r) f =
      ∑ g : Config r zero, EGFConvolution.tupleWeight ((inputs g).map FreeEGF.term)*
        f (EGFConvolution.tupleDegree ((inputs g).map FreeEGF.term)) := by
  rw [coefficients_free_config]
  simp only [key_inputs,weight_inputs]

end ChuShogi.FreeCoordinates
