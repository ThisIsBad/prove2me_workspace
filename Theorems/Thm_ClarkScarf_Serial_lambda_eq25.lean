import Mathlib
import Definitions.Def_ClarkScarf_Serial_Model

open MeasureTheory Set

namespace ClarkScarf.Serial

/-- Eqs. (21)–(25), pp. 483–484: with `n + 1 ≥ 3` periods remaining, critical number `x̄` and
`x₁ + w₁ ≤ x₂ < x̄`, the quantity `Λ` of (21) depends on `x₂` alone and equals (25). -/
theorem lambda_eq25 (M : Model) (n : ℕ) (hn : 2 ≤ n) (xbar : ℝ)
    (hxbar : M.IsCriticalNumber n xbar) (x₁ w₁ x₂ : ℝ) (hdom : x₁ + w₁ ≤ x₂) (hlt : x₂ < xbar) :
    M.c1 * (x₂ - x₁ - w₁) + M.L x₁ +
        M.α * (∫ t in Ioi (0 : ℝ), M.isoCost n (x₁ + w₁ - t) (x₂ - x₁ - w₁) * M.φ t) -
        M.isoCost (n + 1) x₁ w₁ =
      M.c1 * (x₂ - xbar) +
        M.α ^ 2 * (∫ t in Ioi (0 : ℝ), ∫ y in Ioi (0 : ℝ),
          (M.L (x₂ - t - y) - M.L (xbar - t - y)) * M.φ t * M.φ y) +
        M.α * ∫ t in Ioi (0 : ℝ), (M.fLag n (x₂ - t) - M.fLag n (xbar - t)) * M.φ t := by sorry

end ClarkScarf.Serial

