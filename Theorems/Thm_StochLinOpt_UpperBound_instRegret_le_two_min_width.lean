import Mathlib
import Definitions.Def_StochLinOpt_UpperBound_confidenceBall2
import Definitions.Def_StochLinOpt_UpperBound_analysisQuantities

open Matrix

namespace StochLinOpt.UpperBound

theorem instRegret_le_two_min_width {n : ℕ} (D : Set (Fin n → ℝ)) (δ : ℝ)
    (μ xstar : Fin n → ℝ) (x : ℕ → Fin n → ℝ) (ℓ : ℕ → ℝ)
    (hμD : ∀ y ∈ D, |μ ⬝ᵥ y| ≤ 1)
    (hxstar : xstar ∈ D ∧ ∀ y ∈ D, μ ⬝ᵥ xstar ≤ μ ⬝ᵥ y)
    (hrun : IsConfidenceBall2Run D δ x ℓ) (t : ℕ) (ht : 1 ≤ t)
    (hμ : μ ∈ confBall δ x ℓ t) :
    μ ⬝ᵥ x t - μ ⬝ᵥ xstar ≤ 2 * min (Real.sqrt (beta n δ t) * width x t) 1 := by sorry

end StochLinOpt.UpperBound
