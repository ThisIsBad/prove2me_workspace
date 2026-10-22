import Mathlib
import Definitions.Def_NonlinCG_PropStar_Setting

namespace NonlinCG.PropStar

/-- Lemma 4.1 (p. 12). Under Assumptions 2.1, for a run of (1.2)–(1.3) with `β_k ≥ 0`, a line
search satisfying the Zoutendijk condition (2.7) and the sufficient descent condition (4.1), if
the gradients are bounded away from zero (4.3), then `d_k ≠ 0` and
`Σ_{k≥2} ‖u_k − u_{k−1}‖² < ∞` (4.5), where `u_k := d_k/‖d_k‖`. -/
theorem lemma_4_1 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (f : E → ℝ) (hf : ContDiff ℝ 1 f) (β α : ℕ → ℝ) (x d : ℕ → E) (σ₃ : ℝ)
    (hA : NonlinCG.FRBound.Assumptions21 f (x 1)) (hrun : NonlinCG.FRBound.IsCGRun f β α x d)
    (hβ : ∀ k ≥ 2, 0 ≤ β k)
    (hZ : NonlinCG.FRBound.ZoutendijkCondition f x d)
    (hσ₃ : 0 < σ₃ ∧ σ₃ ≤ 1) (hD : SufficientDescent f σ₃ x d)
    (h43 : ∃ γ > 0, ∀ k ≥ 1, γ ≤ ‖NonlinCG.FRBound.g f x k‖) :
    (∀ k ≥ 1, d k ≠ 0) ∧
      Summable (fun k : ℕ => ‖u d (k + 2) - u d (k + 1)‖ ^ 2) := by sorry

end NonlinCG.PropStar

