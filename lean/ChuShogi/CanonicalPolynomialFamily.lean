import ChuShogi.PolynomialFamilyModel
import ChuShogi.PolynomialSelection
import ChuShogi.ComputedConfigurationPartition
import ChuShogi.EvaluatorRefinement

/-! The executable polynomial-choice family for the actual canonical free and
promoted-confined configurations. Matching reuses the previously checked group
models and coordinate inverse laws; no alternative origins are added. -/
namespace ChuShogi.CanonicalPolynomialFamily
open Specification Promotion ConcreteDP CanonicalGroups GroupCoverage GroupConfigurations ConfigurationFactors
open PolynomialFamily PolynomialFamilyModel EGFConvolution

def input {A : Type} [DecidableEq A] (xs : List A) (hn : xs.Nodup) (i : A → FreeEGF.Input) : Family (Member xs) :=
  PolynomialFamily.members xs hn (fun a => (i a).degree) (fun a => 1/((i a).divisor : ℚ))

theorem input_matches {A : Type} [DecidableEq A] (xs : List A) (hn : xs.Nodup) (i : A → FreeEGF.Input) :
    Matches (input xs hn i) (FreeGroupModels.inputModel xs hn i) :=
  PolynomialFamilyModel.members xs hn _ _

def standard := input (stdStates 2) (stdStates_nodup 2) FreeGroupModels.stdInput
def royal (r : Bool) (c : Colour) := input (royalList r c) (royalList_nodup r c) FreeGroupModels.royalInput
def bishop := input bishopStates bishopStates_nodup FreeGroupModels.bishopInput
def kirin := input jumperStates jumperStates_nodup FreeGroupModels.kirinInput
def phoenix := input jumperStates jumperStates_nodup FreeGroupModels.phoenixInput

def side (r : Bool) (c : Colour) : Family (FreeGroupModels.SideData r c) :=
  .product (royal r c) (.product (PolynomialFamily.power standard 10) (.product bishop (.product kirin phoenix)))
def freeData (r : Bool) : Family (FreeGroupModels.Data r) := .product (side r .black) (side r .white)
def free (r : Bool) : Family (Config r ConcreteDP.zero) := .relabel (freeData r) (FreeCoordinates.equivalence r).symm

theorem side_matches (r : Bool) (c : Colour) : Matches (side r c) (FreeGroupModels.side r c) :=
  PolynomialFamilyModel.product (input_matches _ _ _)
    (PolynomialFamilyModel.product (PolynomialFamilyModel.power (input_matches _ _ _) 10)
      (PolynomialFamilyModel.product (input_matches _ _ _)
        (PolynomialFamilyModel.product (input_matches _ _ _) (input_matches _ _ _))))
theorem freeData_matches (r : Bool) : Matches (freeData r) (FreeGroupModels.model r) :=
  PolynomialFamilyModel.product (side_matches r .black) (side_matches r .white)

def pawn (s : Summary) := input (PromotedCoordinates.pawnStates s) (PromotedCoordinates.pawnStates_nodup s) FreeGroupModels.stdInput
def special (cap : Nat) : Family (Fin (cap+1)) := .leaf
  ⟨inferInstance,List.finRange (cap+1),List.nodup_finRange _,List.mem_finRange⟩
  (fun i => ⟨i.val,0,0⟩) (fun i => 1/(i.val.factorial : ℚ))
def promotedData (s : Summary) : Family (PromotedCoordinates.Data s) :=
  .product (pawn s) (.product (special s.bL) (.product (special s.wL) (.product (special s.bRC)
    (.product (special s.wRC) (.product (special s.bGB) (special s.wGB))))))
def promoted (s : Summary) : Family (PromotedChoice s) := .relabel (promotedData s) (PromotedCoordinates.equivalence s).symm

theorem special_matches (cap : Nat) : Matches (special cap) (PromotedCoordinates.typeModel cap) :=
  ⟨rfl,fun _ => rfl,fun _ => rfl⟩
theorem promotedData_matches (s : Summary) : Matches (promotedData s) (PromotedCoordinates.model s) :=
  PolynomialFamilyModel.product (input_matches _ _ _)
    (PolynomialFamilyModel.product (special_matches s.bL)
      (PolynomialFamilyModel.product (special_matches s.wL)
        (PolynomialFamilyModel.product (special_matches s.bRC)
          (PolynomialFamilyModel.product (special_matches s.wRC)
            (PolynomialFamilyModel.product (special_matches s.bGB) (special_matches s.wGB))))))

def configuration (r : Bool) (s : Summary) : Family (Config r s) :=
  .relabel (.product (free r) (promoted s)) (ConfigurationFactors.equivalence r s).symm

theorem free_key (g : Config r ConcreteDP.zero) : key (free r) g =
    tupleDegree ((FreeCoordinates.inputs g).map FreeEGF.term) := by
  change key (freeData r) (FreeCoordinates.toData g)=_
  rw [(freeData_matches r).key,FreeCoordinates.key_inputs]
theorem free_weight (g : Config r ConcreteDP.zero) : weight (free r) g =
    tupleWeight ((FreeCoordinates.inputs g).map FreeEGF.term) := by
  change weight (freeData r) (FreeCoordinates.toData g)=_
  rw [(freeData_matches r).weight,FreeCoordinates.weight_inputs]
theorem promoted_key (p : PromotedChoice s) : key (promoted s) p =
    tupleDegree ((PromotedCoordinates.promotedInputs p).map FreeEGF.term) := by
  change key (promotedData s) (PromotedCoordinates.toData p)=_
  rw [(promotedData_matches s).key,PromotedCoordinates.key_inputs]
theorem promoted_weight (p : PromotedChoice s) : weight (promoted s) p =
    tupleWeight ((PromotedCoordinates.promotedInputs p).map FreeEGF.term) := by
  change weight (promotedData s) (PromotedCoordinates.toData p)=_
  rw [(promotedData_matches s).weight,PromotedCoordinates.weight_inputs]

theorem key_inputs (g : Config r s) : key (configuration r s) g =
    tupleDegree ((CompletionCoefficients.inputs g).map FreeEGF.term) := by
  change EGFConvolution.add (key (free r) (freePart g)) (key (promoted s) (promotedPart g))=_
  rw [free_key,promoted_key,CompletionCoefficients.inputs,List.map_append,CompletionCoefficients.tupleDegree_append]
theorem weight_inputs (g : Config r s) : weight (configuration r s) g =
    tupleWeight ((CompletionCoefficients.inputs g).map FreeEGF.term) := by
  change weight (free r) (freePart g)*weight (promoted s) (promotedPart g)=_
  rw [free_weight,promoted_weight,CompletionCoefficients.inputs,List.map_append,CompletionCoefficients.tupleWeight_append]

theorem free_equivalent (r : Bool) : CoefficientEquivalence.Equivalent (table (free r)) (FreeEGF.coefficients r) := by
  intro test
  change integral (table (freeData r)) test=_
  rw [(freeData_matches r).table,(FreeGroupModels.model r).correct,FreeGroupModels.coefficients_model]
theorem promoted_equivalent (s : Summary) : CoefficientEquivalence.Equivalent (table (promoted s)) (PromotedCoordinates.coefficients s) := by
  intro test
  change integral (table (promotedData s)) test=_
  rw [(promotedData_matches s).table,(PromotedCoordinates.model s).correct,PromotedCoordinates.coefficients_model]
theorem equivalent (r : Bool) (s : Summary) :
    CoefficientEquivalence.Equivalent (table (configuration r s)) (CompletionCoefficients.coefficients r s) := by
  change CoefficientEquivalence.Equivalent (convolve (table (free r)) (table (promoted s)))
    (convolve (FreeEGF.coefficients r) (PromotedCoordinates.coefficients s))
  exact CoefficientEquivalence.convolve_congr _ _ _ _ (free_equivalent r) (promoted_equivalent s)

theorem contribution (g : Config r s) (n0 n1 : Nat) :
    weight (configuration r s) g*CompletionCoefficients.placement n0 n1 (key (configuration r s) g) =
      (ConfigurationFibreCodec.size g n0 n1 : ℚ) := by
  rw [key_inputs,weight_inputs,EvaluatorRefinement.term_refinement,← ConfigurationFibreCodec.size_term]

theorem natural (r : Bool) (s : Summary) (n0 n1 : Nat) :
    PolynomialSelectionWeights.NaturalWeights (configuration r s) (CompletionCoefficients.placement n0 n1) :=
  fun g => ⟨ConfigurationFibreCodec.size g n0 n1,contribution g n0 n1⟩

end ChuShogi.CanonicalPolynomialFamily
