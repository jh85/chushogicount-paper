import ChuShogi.HashAggregation

/-! Exact change of additive summary representation. The projection need not
be injective when the tested weight factors through it; every tuple remains in
the sum. Concrete applications must prove the merge homomorphism. -/
namespace ChuShogi.DPRenaming
open WeightedDP

theorem summary_map (initial : S) (mergeS : S → S → S) (mergeT : T → T → T)
    (feature : A → S) (p : S → T)
    (h : ∀ s t, p (mergeS s t) = mergeT (p s) (p t)) (us : List A) :
    p (summary initial mergeS feature us) =
      summary (p initial) mergeT (fun a => p (feature a)) us := by
  induction us with
  | nil => rfl
  | cons u us ih => simp only [summary,h,ih]

theorem dp_integral_map [DecidableEq S] [DecidableEq T]
    (initial : S) (mergeS : S → S → S) (mergeT : T → T → T) (feature : A → S)
    (p : S → T) (h : ∀ s t, p (mergeS s t) = mergeT (p s) (p t))
    (files : List (List A)) (f : T → Nat) :
    integral (dp (p initial) mergeT (fun a => p (feature a)) files) f =
      integral (dp initial mergeS feature files) (fun s => f (p s)) := by
  rw [dp_integral,dp_integral]
  apply congrArg List.sum
  apply List.map_congr_left
  intro us _
  rw [summary_map initial mergeS mergeT feature p h us]

end ChuShogi.DPRenaming
