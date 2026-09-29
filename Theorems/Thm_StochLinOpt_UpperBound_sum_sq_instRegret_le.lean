import Mathlib
import Definitions.Def_StochLinOpt_UpperBound_confidenceBall2
import Definitions.Def_StochLinOpt_UpperBound_analysisQuantities

open Matrix

namespace StochLinOpt.UpperBound

theorem sum_sq_instRegret_le {n : ℕ} (D : Set (Fin n → ℝ)) (δ : ℝ)
    (μ xstar : Fin n → ℝ) (x : ℕ → Fin n → ℝ) (ℓ : ℕ → ℝ)
    (hD_cube : ∀ y ∈ D, ∀ i, |y i| ≤ 1)
    (hμD : ∀ y ∈ D, |μ ⬝ᵥ y| ≤ 1)
    (hxstar : xstar ∈ D ∧ ∀ y ∈ D, μ ⬝ᵥ xstar ≤ μ ⬝ᵥ y)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hβ₁ : 1 ≤ beta n δ 1)
    (hrun : IsConfidenceBall2Run D δ x ℓ) (T : ℕ)
    (hμ : ∀ t ∈ Finset.Icc 1 T, μ ∈ confBall δ x ℓ t) :
    ∑ t ∈ Finset.Icc 1 T, (μ ⬝ᵥ x t - μ ⬝ᵥ xstar) ^ 2 ≤
      8 * n * beta n δ T * Real.log (T + 1) := by sorry

end StochLinOpt.UpperBound
