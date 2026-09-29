import Definitions.Def_Roberts1997_RWM_Target

open MeasureTheory ProbabilityTheory Filter
open scoped ContDiff

namespace Roberts1997.RWM

/-- Lemma 2.5 (pp. 115–116). For `V ∈ C_c^∞`,
`limsup_{n→∞} sup_{x₁ ∈ ℝ} n |𝔼[V(Y₁) - V(x₁)]| < ∞` with `Y₁ ~ N(x₁, σ_n²)`; stated as
eventual uniform boundedness. -/
theorem gaussian_increment_bounded (V : ℝ → ℝ) (hV : ContDiff ℝ ∞ V)
    (hVc : HasCompactSupport V) (l : ℝ) (hl : 0 < l) :
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, ∀ x₁ : ℝ,
      (n : ℝ) * |∫ y, (V y - V x₁) ∂(gaussianReal x₁ (sigmaSq n l).toNNReal)| ≤ C := by sorry

end Roberts1997.RWM
