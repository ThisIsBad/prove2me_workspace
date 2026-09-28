import Mathlib
import Definitions.Def_WorstCaseVaR_Entropy_Basic

namespace WorstCaseVaR.Entropy

/-- Eq. (48), p. 554: for `λ > 0` and `0 ≤ φ ≤ 1`, the infimum over `λ₀ ∈ ℝ` of
`θ(λ₀, λ) = λ₀ + λd + λe^{-λ₀/λ-1}((e^{1/λ} - 1)φ + 1)` is `λd + λ log((e^{1/λ} - 1)φ + 1)`,
and it is attained. -/
theorem inf_dual_over_lambda0 (d φ lam : ℝ) (hlam : 0 < lam) (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1) :
    IsLeast
      (Set.range fun lam0 : ℝ =>
        lam0 + lam * d + lam * Real.exp (-(lam0 / lam) - 1) * ((Real.exp (1 / lam) - 1) * φ + 1))
      (dualValue d φ lam) := by sorry

end WorstCaseVaR.Entropy
