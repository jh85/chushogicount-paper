import ChuShogi.ReducedGeometry

/-! Reindex canonical pawn multiplicities by their total, without selecting
origins. In the default compact summary both individual bounds equal the joint
bound, and the source `tok` coefficient is exactly a binomial sum. -/
namespace ChuShogi.PawnDiagonal
open EGFConvolution CanonicalGroups ReducedGeometry

def states (j : Nat) : List (Nat × Nat) :=
  (List.range (j+1)).flatMap fun t => (List.range (t+1)).map fun b => (b,t-b)

theorem states_iff (j b w : Nat) : (b,w) ∈ states j ↔ b+w ≤ j := by
  simp only [states,List.mem_flatMap,List.mem_map,List.mem_range,Prod.mk.injEq]
  constructor
  · rintro ⟨t,ht,u,hu,rfl,rfl⟩; omega
  · intro h; exact ⟨b+w,by omega,b,by omega,rfl,by omega⟩

theorem states_nodup (j : Nat) : (states j).Nodup := by
  simp only [states,List.nodup_iff_pairwise_ne,List.pairwise_flatMap,List.pairwise_map]
  constructor
  · intro t _
    apply List.Pairwise.imp _ List.nodup_range
    intro b c hbc heq
    exact hbc (Prod.mk.inj heq).1
  · apply List.Pairwise.imp_of_mem _ List.nodup_range
    intro t u ht hu htu a ha b hb heq
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp ha
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hb
    have hv' := List.mem_range.mp hv
    have hw' := List.mem_range.mp hw
    have he := Prod.mk.inj heq
    exact htu (by omega)

theorem states_perm (j : Nat) : (stdStates j).Perm (states j) := by
  apply (List.perm_ext_iff_of_nodup (stdStates_nodup j) (states_nodup j)).mpr
  rintro ⟨b,w⟩
  rw [stdStates_iff,states_iff]

theorem pawn_states (j : Nat) : PromotedCoordinates.pawnStates (pawnSummary j) = stdStates j := by
  apply List.filter_eq_self.mpr
  intro v hv
  have h := (stdStates_iff j v.1 v.2).mp hv
  change decide (v.1 ≤ j ∧ v.2 ≤ j) = true
  exact decide_eq_true (by omega)

theorem choose_sum (t : Nat) : ((List.range (t+1)).map (Nat.choose t)).sum = 2^t := by
  rw [← List.sum_toFinset _ List.nodup_range,List.toFinset_range,Nat.sum_range_choose]

theorem tok_full (j t : Nat) (h : t ≤ j) : PromotedEGF.tok j j j t = 2^t := by
  unfold PromotedEGF.tok
  rw [ite_eq_left h]
  have he : ((List.range (t+1)).map fun b => if b ≤ j ∧ t-b ≤ j then t.choose b else 0) =
      (List.range (t+1)).map (Nat.choose t) := by
    apply List.map_congr_left
    intro b hb
    have hb' := List.mem_range.mp hb
    rw [ite_eq_left (show b ≤ j ∧ t-b ≤ j by omega)]
  rw [he,choose_sum]

theorem pawn_integral (j : Nat) (f : Degree → ℚ) :
    integral (PromotedCoordinates.pawnTable (pawnSummary j)) f =
      ((List.range (j+1)).map fun t => ((2^t : Nat) : ℚ)/(t.factorial : ℚ)*f (ScaledPolynomials.lift t)).sum := by
  unfold PromotedCoordinates.pawnTable
  rw [pawn_states]
  unfold integral
  rw [List.map_map,(states_perm j).map _ |>.sum_eq]
  simp only [states,List.map_flatMap,sum_flatMap,List.map_map,Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t _
  have he : ((List.range (t+1)).map fun b =>
      (FreeEGF.term (FreeGroupModels.stdInput (b,t-b))).2 * f (FreeEGF.term (FreeGroupModels.stdInput (b,t-b))).1) =
      (List.range (t+1)).map fun b => (t.choose b : ℚ)*((1/(t.factorial : ℚ))*f (ScaledPolynomials.lift t)) := by
    apply List.map_congr_left
    intro b hb
    have hbt : b ≤ t := by have := List.mem_range.mp hb; omega
    have hfac : (t.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero t
    have h := EGFArithmetic.binomial_egf b (t-b)
    rw [Nat.add_sub_of_le hbt] at h
    simp only [FreeEGF.term,FreeGroupModels.stdInput,Nat.cast_mul,Nat.add_sub_of_le hbt]
    rw [h]
    dsimp [ScaledPolynomials.lift]
    field_simp
  rw [he]
  have hc : (((List.range (t+1)).map fun b => (t.choose b : ℚ)).sum) = ((2^t : Nat) : ℚ) := by
    simpa only [Nat.cast_list_sum,List.map_map,Function.comp_def] using
      congrArg (fun n : Nat => (n : ℚ)) (choose_sum t)
  simp_rw [mul_comm (↑(t.choose _) : ℚ)]
  rw [← mul_list_sum,hc]
  ring

end ChuShogi.PawnDiagonal
