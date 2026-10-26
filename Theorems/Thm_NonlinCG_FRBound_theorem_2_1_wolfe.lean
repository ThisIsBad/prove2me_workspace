import Mathlib
import Definitions.Def_NonlinCG_FRBound_Setting

namespace NonlinCG.FRBound

/-- Theorem 2.1 (i) (Gilbert–Nocedal, INRIA RR-1268, p. 4): under Assumptions 2.1, any iteration
`x_{k+1} = x_k + α_k d_k` (1.3) with positive steplengths, descent directions `d_k` and
steplengths satisfying the Wolfe conditions (2.4)–(2.5) with `0 < σ₁ < σ₂ < 1` satisfies the
Zoutendijk condition (2.7). The directions `d_k` are arbitrary, not necessarily (1.2). -/
theorem theorem_2_1_wolfe {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E → ℝ) (hf : ContDiff ℝ 1 f) (α : ℕ → ℝ) (x d : ℕ → E)
    (σ₁ σ₂ : ℝ) (hA : Assumptions21 f (x 1))
    (hσ : 0 < σ₁ ∧ σ₁ < σ₂ ∧ σ₂ < 1)
    (hiter : ∀ k ≥ 1, 0 < α k ∧ x (k + 1) = x k + α k • d k)
    (hdesc : ∀ k ≥ 1, inner ℝ (g f x k) (d k) < 0)
    (hls : ∀ k ≥ 1, WolfeStep f σ₁ σ₂ (x k) (d k) (α k)) :
    ZoutendijkCondition f x d := by sorry

end NonlinCG.FRBound

