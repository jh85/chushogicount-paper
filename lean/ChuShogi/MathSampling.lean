module
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

@[expose] public section
namespace ChuShogi.MathSampling

/-- Conditional uniformity under any proved bijection, with an actual input PMF. -/
theorem uniform_equiv {A B : Type} (e : A ≃ B) (p : PMF A) (v : ENNReal)
    (h : ∀ a, p a = v) (b : B) : (p.map e) b = v := by
  classical
  rw [PMF.map_apply]
  have hh (a : A) : b = e a ↔ a = e.symm b := by
    constructor
    · intro he
      have hr := congrArg e.symm he
      rw [e.symm_apply_apply] at hr
      exact hr.symm
    · intro he; subst a; exact (e.apply_symm_apply b).symm
  simp only [hh]
  simpa using h (e.symm b)

end ChuShogi.MathSampling
