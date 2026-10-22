import Mathlib
import Definitions.Def_NonlinCG_PropStar_Setting

namespace NonlinCG.PropStar

/-- Lemma 4.2 (p. 14). Under Assumptions 2.1, for a run of (1.2)–(1.3) with a line search
satisfying (4.4), the Zoutendijk condition (2.7) and the sufficient descent condition (4.1), with
Property (*), and with (4.3), there is `λ > 0` such that for every `Δ ≥ 1` and every index `k₀`
some `k ≥ k₀` has `|𝒦^λ_{k,Δ}| > Δ/2`. No sign condition on `β_k` is assumed. -/
theorem lemma_4_2 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (f : E → ℝ) (hf : ContDiff ℝ 1 f) (β α : ℕ → ℝ) (x d : ℕ → E) (σ₃ : ℝ)
    (hA : NonlinCG.FRBound.Assumptions21 f (x 1)) (hrun : NonlinCG.FRBound.IsCGRun f β α x d)
    (hL : ∀ k ≥ 1, x k ∈ NonlinCG.FRBound.levelSet f (x 1))
    (hZ : NonlinCG.FRBound.ZoutendijkCondition f x d)
    (hσ₃ : 0 < σ₃ ∧ σ₃ ≤ 1) (hD : SufficientDescent f σ₃ x d)
    (hP : PropertyStar f β x)
    (h43 : ∃ γ > 0, ∀ k ≥ 1, γ ≤ ‖NonlinCG.FRBound.g f x k‖) :
    ∃ lam > 0, ∀ Δ : ℕ, 1 ≤ Δ → ∀ k₀ : ℕ, ∃ k ≥ k₀, Δ < 2 * (Kset lam x k Δ).card := by sorry

end NonlinCG.PropStar

