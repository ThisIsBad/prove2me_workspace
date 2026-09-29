import Mathlib
import Definitions.Def_LiuVanRyzin_Model

namespace LiuVanRyzin

/-- Proposition 1 (Liu–van Ryzin 2008, p. 1120). For every fill rate `q ∈ [0, 1)` the threshold
`v(q) ≥ p₁` exists and is unique: valuations above it buy in period 1, valuations below it wait. -/
theorem cutoff_exists_unique (u : ℝ → ℝ) (hu : IsCustomerUtility u) (p₁ p₂ : ℝ)
    (hp : p₂ < p₁) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    p₁ ≤ cutoff u p₁ p₂ q ∧
      (∀ v : ℝ, cutoff u p₁ p₂ q < v → buysEarly u p₁ p₂ q v) ∧
      (∀ v : ℝ, v < cutoff u p₁ p₂ q → ¬ buysEarly u p₁ p₂ q v) ∧
      (∀ t : ℝ, p₁ ≤ t → (∀ v : ℝ, t < v → buysEarly u p₁ p₂ q v) →
        (∀ v : ℝ, v < t → ¬ buysEarly u p₁ p₂ q v) → t = cutoff u p₁ p₂ q) := by sorry

end LiuVanRyzin
