import ChuShogi.IntegerCompletion

/-! Promoted-confined coefficients have no bound-class degree. Factorial-scaled
coefficients are natural multinomial sums for arbitrary capacities. -/
namespace ChuShogi.PromotedCoefficientSupport
open EGFConvolution PromotedCoordinates

def LiftOnly (t : Table) : Prop := ∀ e∈t, e.1=ScaledPolynomials.lift e.1.m

theorem insert_lift (d : Degree) (w : ℚ) (t : Table) (hd : d=ScaledPolynomials.lift d.m)
    (ht : LiftOnly t) : LiftOnly (EGFConvolution.insert d w t) := by
  induction t with
  | nil => intro e he; simp only [EGFConvolution.insert,List.mem_singleton] at he; subst e; exact hd
  | cons v t ih =>
    have hv := ht v (by simp)
    have hh : LiftOnly t := fun e he => ht e (by simp [he])
    simp only [EGFConvolution.insert]
    split
    · intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact hv
      · exact hh e he
    · intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact hv
      · exact ih hh e he

theorem convolve_lift (a b : Table) (ha : LiftOnly a) (hb : LiftOnly b) : LiftOnly (convolve a b) := by
  have inner (e : Term) (he : e.1=ScaledPolynomials.lift e.1.m) (out : Table) (ho : LiftOnly out) :
      LiftOnly (b.foldr (fun v out => EGFConvolution.insert (add e.1 v.1) (e.2*v.2) out) out) := by
    induction b with
    | nil => exact ho
    | cons v b ih =>
      apply insert_lift
      · have hv := hb v (by simp)
        rw [he,hv]
        rfl
      · exact ih (fun v hv => hb v (by simp [hv]))
  induction a with
  | nil => intro e he; cases he
  | cons e a ih =>
    exact inner e (ha e (by simp)) _ (ih (fun v hv => ha v (by simp [hv])))

theorem product_lift (ts : List Table) (h : ∀ t∈ts, LiftOnly t) : LiftOnly (product ts) := by
  induction ts with
  | nil => intro e he; simp only [product,List.mem_singleton] at he; subst e; rfl
  | cons t ts ih => exact convolve_lift t (product ts) (h t (by simp)) (ih (fun t ht => h t (by simp [ht])))

theorem pawn_lift (s : ConcreteDP.Summary) : LiftOnly (pawnTable s) := by
  intro e he
  obtain ⟨v,_,rfl⟩ := List.mem_map.mp he
  rfl

theorem type_lift (n : Nat) : LiftOnly (typeTable n) := by
  intro e he
  obtain ⟨v,_,rfl⟩ := List.mem_map.mp he
  rfl

theorem coefficients_lift (s : ConcreteDP.Summary) : LiftOnly (coefficients s) := by
  apply product_lift
  intro t ht
  simp only [tables,List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pawn_lift s
  all_goals exact type_lift _

theorem pawn_integral (s : ConcreteDP.Summary) : IntegralTable (pawnTable s) := by
  intro e he
  obtain ⟨⟨b,w⟩,_,rfl⟩ := List.mem_map.mp he
  apply FreeEGF.term_integral
  exact ⟨Nat.mul_ne_zero (Nat.factorial_ne_zero b) (Nat.factorial_ne_zero w),Nat.factorial_mul_factorial_dvd_factorial_add b w⟩

theorem type_integral (n : Nat) : IntegralTable (typeTable n) := by
  intro e he
  obtain ⟨v,_,rfl⟩ := List.mem_map.mp he
  refine ⟨1,?_⟩
  change (1/(v.val.factorial : ℚ))*(v.val.factorial : ℚ)=1
  have hn : (v.val.factorial : ℚ)≠0 := by exact_mod_cast Nat.factorial_ne_zero v.val
  field_simp

theorem coefficients_integral (s : ConcreteDP.Summary) : IntegralTable (coefficients s) := by
  apply product_integral
  intro t ht
  simp only [tables,List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pawn_integral s
  all_goals exact type_integral _

def labelled (s : ConcreteDP.Summary) : List (Nat × Nat) :=
  (coefficients s).map fun e => (e.1.m,(e.2*(e.1.m.factorial : ℚ)).num.toNat)

theorem labelled_conversion (s : ConcreteDP.Summary) (e : Term) (he : e∈coefficients s) :
    (((e.2*(e.1.m.factorial : ℚ)).num.toNat : Nat) : ℚ)=e.2*(e.1.m.factorial : ℚ) := by
  obtain ⟨n,hn⟩ := coefficients_integral s e he
  rw [hn]
  simp

end ChuShogi.PromotedCoefficientSupport
