import ChuShogi.FreeCoordinates

/-! Exact present-multiplicity coordinates for promoted confined roles.
The pawn pair keeps the joint limit. Every other type is chosen once from its
capacity interval; eligible original slots are not independently labelled.
-/
namespace ChuShogi.PromotedCoordinates
open Specification Promotion ConcreteDP SummaryBridge CanonicalGroups GroupConfigurations ConfigurationFactors
open FiniteCoefficientModel EGFConvolution

def pawnStates (s : Summary) : List (Nat × Nat) :=
  (stdStates s.joint).filter fun v => decide (v.1 ≤ s.cb ∧ v.2 ≤ s.cw)

theorem pawnStates_iff (s : Summary) (b w : Nat) : (b,w) ∈ pawnStates s ↔
    b+w ≤ s.joint ∧ b ≤ s.cb ∧ w ≤ s.cw := by
  simp [pawnStates,stdStates_iff]

theorem pawnStates_nodup (s : Summary) : (pawnStates s).Nodup := (stdStates_nodup _).filter _

abbrev Data (s : Summary) := Member (pawnStates s) ×
  (Fin (s.bL+1) × (Fin (s.wL+1) × (Fin (s.bRC+1) ×
    (Fin (s.wRC+1) × (Fin (s.bGB+1) × Fin (s.wGB+1))))))

def toData (p : PromotedChoice s) : Data s :=
  (⟨(p.n .black .pawn,p.n .white .pawn),(pawnStates_iff s _ _).mpr ⟨p.joint,p.black,p.white⟩⟩,
   ⟨p.n .black .lance,promoted_bound p .black .lance⟩,
   ⟨p.n .white .lance,promoted_bound p .white .lance⟩,
   ⟨p.n .black .chariot,promoted_bound p .black .chariot⟩,
   ⟨p.n .white .chariot,promoted_bound p .white .chariot⟩,
   ⟨p.n .black .goBetween,promoted_bound p .black .goBetween⟩,
   ⟨p.n .white .goBetween,promoted_bound p .white .goBetween⟩)

def fromData (d : Data s) : PromotedChoice s where
  n c k := match c,k with
    | .black,.pawn => d.1.val.1
    | .white,.pawn => d.1.val.2
    | .black,.lance => d.2.1.val
    | .white,.lance => d.2.2.1.val
    | .black,.chariot => d.2.2.2.1.val
    | .white,.chariot => d.2.2.2.2.1.val
    | .black,.goBetween => d.2.2.2.2.2.1.val
    | .white,.goBetween => d.2.2.2.2.2.2.val
  black := ((pawnStates_iff s _ _).mp d.1.property).2.1
  white := ((pawnStates_iff s _ _).mp d.1.property).2.2
  joint := ((pawnStates_iff s _ _).mp d.1.property).1
  nonpawn := by
    intro c k hk
    cases c <;> cases k
    · contradiction
    · exact Nat.le_of_lt_succ d.2.1.isLt
    · exact Nat.le_of_lt_succ d.2.2.2.1.isLt
    · exact Nat.le_of_lt_succ d.2.2.2.2.2.1.isLt
    · contradiction
    · exact Nat.le_of_lt_succ d.2.2.1.isLt
    · exact Nat.le_of_lt_succ d.2.2.2.2.1.isLt
    · exact Nat.le_of_lt_succ d.2.2.2.2.2.2.isLt

theorem promoted_ext (p q : PromotedChoice s) (h : p.n = q.n) : p = q := by
  cases p; cases q; cases h; rfl

theorem from_to (p : PromotedChoice s) : fromData (toData p) = p := by
  have hn : (fromData (toData p)).n = p.n := by funext c k; cases c <;> cases k <;> rfl
  exact promoted_ext _ _ hn

theorem to_from (d : Data s) : toData (fromData d) = d := rfl

def equivalence (s : Summary) : PromotedChoice s ≃ Data s := ⟨toData,fromData,from_to,to_from⟩

noncomputable def pawnModel (s : Summary) : Model (Member (pawnStates s)) :=
  FreeGroupModels.inputModel (pawnStates s) (pawnStates_nodup s) FreeGroupModels.stdInput

noncomputable def typeModel (cap : Nat) : Model (Fin (cap+1)) :=
  fromList (List.finRange (cap+1)) (List.nodup_finRange _) (fun _ => by simp)
    (fun i => ⟨i.val,0,0⟩) (fun i => 1/(i.val.factorial : ℚ))

noncomputable def model (s : Summary) : Model (Data s) :=
  FiniteCoefficientModel.product (pawnModel s)
    (FiniteCoefficientModel.product (typeModel s.bL)
      (FiniteCoefficientModel.product (typeModel s.wL)
        (FiniteCoefficientModel.product (typeModel s.bRC)
          (FiniteCoefficientModel.product (typeModel s.wRC)
            (FiniteCoefficientModel.product (typeModel s.bGB) (typeModel s.wGB))))))

def promotedInputs (p : PromotedChoice s) : List FreeEGF.Input :=
  [FreeGroupModels.stdInput (p.n .black .pawn,p.n .white .pawn)] ++
    [⟨⟨p.n .black .lance,0,0⟩,(p.n .black .lance).factorial⟩,
     ⟨⟨p.n .white .lance,0,0⟩,(p.n .white .lance).factorial⟩,
     ⟨⟨p.n .black .chariot,0,0⟩,(p.n .black .chariot).factorial⟩,
     ⟨⟨p.n .white .chariot,0,0⟩,(p.n .white .chariot).factorial⟩,
     ⟨⟨p.n .black .goBetween,0,0⟩,(p.n .black .goBetween).factorial⟩,
     ⟨⟨p.n .white .goBetween,0,0⟩,(p.n .white .goBetween).factorial⟩]

theorem key_inputs (p : PromotedChoice s) : (model s).key (toData p) =
    tupleDegree ((promotedInputs p).map FreeEGF.term) := by
  simp [model,FiniteCoefficientModel.product,pawnModel,typeModel,fromList,
    FreeGroupModels.inputModel,members,toData,promotedInputs,FreeGroupModels.stdInput,
    FreeEGF.term,tupleDegree,CoefficientEquivalence.degree_add_zero]

theorem weight_inputs (p : PromotedChoice s) : (model s).weight (toData p) =
    tupleWeight ((promotedInputs p).map FreeEGF.term) := by
  simp [model,FiniteCoefficientModel.product,pawnModel,typeModel,fromList,
    FreeGroupModels.inputModel,members,toData,promotedInputs,FreeGroupModels.stdInput,
    FreeEGF.term,tupleWeight,mul_assoc]

def pawnTable (s : Summary) : Table := (pawnStates s).map fun v => FreeEGF.term (FreeGroupModels.stdInput v)

def typeTable (cap : Nat) : Table := (List.finRange (cap+1)).map fun i => (⟨i.val,0,0⟩,1/(i.val.factorial : ℚ))

def tables (s : Summary) : List Table :=
  [pawnTable s,typeTable s.bL,typeTable s.wL,typeTable s.bRC,typeTable s.wRC,typeTable s.bGB,typeTable s.wGB]

/-- Executable rational polynomial for all present promoted-confined counts. -/
def coefficients (s : Summary) : Table := EGFConvolution.product (tables s)

theorem pawn_table (s : Summary) : (pawnModel s).table = pawnTable s := by
  rw [pawnModel,FreeGroupModels.inputModel_table]
  simp only [pawnTable,List.map_map]
  rfl

theorem type_table (cap : Nat) : (typeModel cap).table = typeTable cap := rfl

theorem coefficients_model (s : Summary) (f : Degree → ℚ) :
    integral (coefficients s) f = ∑ q : Data s, (model s).weight q*f ((model s).key q) := by
  have he : integral (coefficients s) f = integral (model s).table f := by
    dsimp only [model,FiniteCoefficientModel.product]
    rw [pawn_table,type_table,type_table,type_table,type_table,type_table,type_table]
    simp only [coefficients,tables,EGFConvolution.product]
    simp_rw [integral_convolve]
    simp only [CoefficientEquivalence.integral_unit,CoefficientEquivalence.degree_add_zero]
  exact he.trans ((model s).correct f)

theorem coefficients_canonical (s : Summary) (f : Degree → ℚ) :
    integral (coefficients s) f = ∑ p : PromotedChoice s,
      tupleWeight ((promotedInputs p).map FreeEGF.term)*f (tupleDegree ((promotedInputs p).map FreeEGF.term)) := by
  rw [coefficients_model]
  have he := Fintype.sum_equiv (equivalence s).symm
    (fun q => (model s).weight q*f ((model s).key q))
    (fun p => (model s).weight (toData p)*f ((model s).key (toData p))) (fun d => by
      change (model s).weight d*f ((model s).key d) =
        (model s).weight (toData (fromData d))*f ((model s).key (toData (fromData d)))
      rw [to_from])
  rw [he]
  simp only [key_inputs,weight_inputs]

end ChuShogi.PromotedCoordinates
