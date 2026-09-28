import Mathlib
import Definitions.Def_GoldenRatioVI_Fixed_IsGRAALRun
open scoped goldenRatio

namespace GoldenRatioVI.Fixed

/-- Eq. (12): if `z̄ᵏ = ((φ - 1) zᵏ + z̄ᵏ⁻¹) / φ` for all `k ≥ 1`, then for every point `z*`
and every `k`,
`‖zᵏ⁺¹ - z*‖² = (1+φ)‖z̄ᵏ⁺¹ - z*‖² - φ‖z̄ᵏ - z*‖² + φ(1+φ)‖z̄ᵏ⁺¹ - z̄ᵏ‖²
             = (1+φ)‖z̄ᵏ⁺¹ - z*‖² - φ‖z̄ᵏ - z*‖² + (1/φ)‖zᵏ⁺¹ - z̄ᵏ‖²`. -/
theorem norm_sq_identity {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (z zbar : ℕ → E) (hbar : IsGoldenAveraging z zbar) (zs : E) (k : ℕ) :
    ‖z (k + 1) - zs‖ ^ 2 =
        (1 + φ) * ‖zbar (k + 1) - zs‖ ^ 2 - φ * ‖zbar k - zs‖ ^ 2
          + φ * (1 + φ) * ‖zbar (k + 1) - zbar k‖ ^ 2 ∧
      ‖z (k + 1) - zs‖ ^ 2 =
        (1 + φ) * ‖zbar (k + 1) - zs‖ ^ 2 - φ * ‖zbar k - zs‖ ^ 2
          + (1 / φ) * ‖z (k + 1) - zbar k‖ ^ 2 := by sorry

end GoldenRatioVI.Fixed

