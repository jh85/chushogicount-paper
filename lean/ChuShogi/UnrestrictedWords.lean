module
public import ChuShogi.EGFArithmetic

@[expose] public section

/-! Counting unrestricted canonical words with empty squares. The specified
role counts are independent of any generating function or recurrence. -/
namespace ChuShogi.UnrestrictedWords
open scoped Classical
open MultinomialPlacements EGFArithmetic

variable {S R : Type} [Fintype S] [Fintype R] [DecidableEq R]

def sigmaFibre (n : R → Nat) (r : R) : {x : Σ a, Fin (n a) // x.1 = r} ≃ Fin (n r) where
  toFun x := x.property ▸ x.val.2
  invFun i := ⟨⟨r,i⟩,rfl⟩
  left_inv := by rintro ⟨⟨a,i⟩,h⟩; cases h; rfl
  right_inv := fun _ => rfl

/-- A finite count profile is realizable exactly when its total is the domain
size. This constructs a witness rather than assuming a feasible profile. -/
theorem realizes_iff (n : R → Nat) :
    (∃ f : S → R, multiplicity f = n) ↔ ∑ r, n r = Fintype.card S := by
  constructor
  · rintro ⟨f,rfl⟩
    exact sum_multiplicities f
  · intro hn
    have hc : Fintype.card (Σ r, Fin (n r)) = Fintype.card S := by
      simpa using hn
    let e : S ≃ Σ r, Fin (n r) := Fintype.equivOfCardEq hc.symm
    refine ⟨fun s => (e s).1,?_⟩
    funext r
    have ef : {s : S // (e s).1 = r} ≃ Fin (n r) :=
      (Equiv.subtypeEquiv e (fun _ => Iff.rfl)).trans (sigmaFibre n r)
    exact (Fintype.card_congr ef).trans (Fintype.card_fin _)

def SomeCounts (n : R → Nat) (f : S → Option R) : Prop :=
  ∀ r, multiplicity f (some r) = n r

theorem some_sum (f : S → Option R) :
    multiplicity f none + ∑ r, multiplicity f (some r) = Fintype.card S := by
  simpa only [Fintype.sum_option] using sum_multiplicities f

/-- The exact rational EGF evaluation equals an integer cardinality. The empty
role is implicit in the falling factorial; overfull multiplicities give zero. -/
theorem some_counts_egf [DecidableEq S] (n : R → Nat) :
    (Fintype.card {f : S → Option R // SomeCounts n f} : ℚ) =
      ((Fintype.card S).descFactorial (∑ r, n r) : ℚ)*inverseFactorials n := by
  let m := ∑ r, n r
  let fsize := Fintype.card S
  by_cases hm : m ≤ fsize
  · let q : Option R → Nat := fun o => match o with | none => fsize-m | some r => n r
    have hq : ∑ o, q o = fsize := by simp only [Fintype.sum_option,q]; omega
    obtain ⟨f,hf⟩ := (realizes_iff (S := S) q).mpr hq
    have hp (g : S → Option R) : SomeCounts n g ↔ SameCounts f g := by
      constructor
      · intro hg o
        rw [show multiplicity f o = q o from congrFun hf o]
        cases o with
        | some r => exact hg r
        | none =>
          have he := some_sum g
          have hn : (∑ r, multiplicity g (some r)) = m := Finset.sum_congr rfl (fun r _ => hg r)
          rw [hn] at he
          change multiplicity g none = fsize-m
          omega
      · intro hg r
        exact (hg (some r)).trans (congrFun hf (some r))
    have eqv : {g : S → Option R // SomeCounts n g} ≃ {g : S → Option R // SameCounts f g} :=
      Equiv.subtypeEquiv (Equiv.refl _) hp
    rw [Fintype.card_congr eqv,fixed_counts_multinomial,hf,← factorial_scaling q,hq]
    have hfac : ((fsize-m).factorial : ℚ)*((fsize.descFactorial m) : ℚ) = (fsize.factorial : ℚ) := by
      exact_mod_cast Nat.factorial_mul_descFactorial hm
    change (fsize.factorial : ℚ)*inverseFactorials q = (fsize.descFactorial m : ℚ)*inverseFactorials n
    rw [← hfac]
    simp only [inverseFactorials,Fintype.prod_option,q]
    have hnz : ((fsize-m).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (fsize-m)
    field_simp
  · have hempty : IsEmpty {f : S → Option R // SomeCounts n f} := ⟨fun f => by
      have he := some_sum f.val
      have hn : (∑ r, multiplicity f.val (some r)) = m :=
        Finset.sum_congr rfl (fun r _ => f.property r)
      rw [hn] at he
      omega⟩
    rw [Fintype.card_eq_zero_iff.mpr hempty]
    have hz : fsize.descFactorial m = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
    change (0 : ℚ) = (fsize.descFactorial m : ℚ)*inverseFactorials n
    rw [hz,Nat.cast_zero,zero_mul]

def joinWords {T : Type} (w : (S → Option R) × (T → Option R)) : S ⊕ T → Option R :=
  Sum.elim w.1 w.2

omit [Fintype R] in
theorem join_multiplicity {T : Type} [Fintype T]
    (w : (S → Option R) × (T → Option R)) (r : R) :
    multiplicity (joinWords w) (some r) = multiplicity w.1 (some r) + multiplicity w.2 (some r) := by
  let eqv : {s : S ⊕ T // joinWords w s = some r} ≃
      {s : S // w.1 s = some r} ⊕ {s : T // w.2 s = some r} := {
    toFun := fun s => match s with
      | ⟨.inl x,h⟩ => .inl ⟨x,h⟩
      | ⟨.inr x,h⟩ => .inr ⟨x,h⟩
    invFun := fun s => match s with
      | .inl x => ⟨.inl x.val,x.property⟩
      | .inr x => ⟨.inr x.val,x.property⟩
    left_inv := by rintro ⟨x,h⟩; cases x <;> rfl
    right_inv := by intro x; cases x <;> rfl }
  exact (Fintype.card_congr eqv).trans Fintype.card_sum

/-- All unrestricted class splits are summed, leaving only the total number
of available squares. This is the word-level Vandermonde refinement. -/
theorem two_class_some_counts_egf {T : Type} [Fintype T] [DecidableEq S] [DecidableEq T]
    (n : R → Nat) :
    (Fintype.card {w : (S → Option R) × (T → Option R) //
      ∀ r, multiplicity w.1 (some r) + multiplicity w.2 (some r) = n r} : ℚ) =
      ((Fintype.card S+Fintype.card T).descFactorial (∑ r, n r) : ℚ)*inverseFactorials n := by
  let eqv : ((S → Option R) × (T → Option R)) ≃ (S ⊕ T → Option R) := {
    toFun := joinWords
    invFun := fun f => (fun s => f (.inl s),fun t => f (.inr t))
    left_inv := fun _ => rfl
    right_inv := by intro f; funext s; cases s <;> rfl }
  let subeqv : {w : (S → Option R) × (T → Option R) //
      ∀ r, multiplicity w.1 (some r)+multiplicity w.2 (some r)=n r} ≃
      {f : S ⊕ T → Option R // SomeCounts n f} := Equiv.subtypeEquiv eqv (fun w => by
    simp only [SomeCounts,show eqv w = joinWords w from rfl,join_multiplicity])
  rw [Fintype.card_congr subeqv,some_counts_egf,Fintype.card_sum]

end ChuShogi.UnrestrictedWords
