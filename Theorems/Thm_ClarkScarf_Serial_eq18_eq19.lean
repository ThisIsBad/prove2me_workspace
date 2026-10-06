import Mathlib
import Definitions.Def_ClarkScarf_Serial_Model

open MeasureTheory Set

namespace ClarkScarf.Serial

/-- Eqs. (18)–(19), p. 483: if (16) holds with `n` periods remaining for a function `G` of
echelon stock, and `x̄` is a critical number of the isolated problem with `n + 1` periods
remaining, then with `Z(x₂) = inf_{z ≥ 0} {c(z) + L̃(x₂) + α ∫₀^∞ G(x₂ + z - t) φ(t) dt}`:
for `x₂ ≥ x̄`, `C_{n+1}(x₁, w₁, x₂) = Ĉ_{n+1}(x₁, w₁) + Z(x₂)` (18); for `x₂ < x̄`,
`C_{n+1}(x₁, w₁, x₂) = c₁(x₂ - x₁ - w₁) + L(x₁) + α ∫₀^∞ Ĉ_n(x₁ + w₁ - t, x₂ - x₁ - w₁) φ(t) dt
+ Z(x₂)` (19). -/
theorem eq18_eq19 (M : Model) (n : ℕ) (G : ℝ → ℝ)
    (hG : ∀ x₁ w₁ x₂ : ℝ, x₁ + w₁ ≤ x₂ → M.sysCost n x₁ w₁ x₂ = M.isoCost n x₁ w₁ + G x₂)
    (xbar : ℝ) (hxbar : M.IsCriticalNumber n xbar)
    (x₁ w₁ x₂ : ℝ) (hdom : x₁ + w₁ ≤ x₂) :
    (xbar ≤ x₂ →
      M.sysCost (n + 1) x₁ w₁ x₂ = M.isoCost (n + 1) x₁ w₁ +
        ⨅ z : {z : ℝ // 0 ≤ z}, (M.orderCost (z : ℝ) + M.Lt x₂ +
          M.α * ∫ t in Ioi (0 : ℝ), G (x₂ + (z : ℝ) - t) * M.φ t)) ∧
    (x₂ < xbar →
      M.sysCost (n + 1) x₁ w₁ x₂ = M.c1 * (x₂ - x₁ - w₁) + M.L x₁ +
        M.α * (∫ t in Ioi (0 : ℝ), M.isoCost n (x₁ + w₁ - t) (x₂ - x₁ - w₁) * M.φ t) +
        ⨅ z : {z : ℝ // 0 ≤ z}, (M.orderCost (z : ℝ) + M.Lt x₂ +
          M.α * ∫ t in Ioi (0 : ℝ), G (x₂ + (z : ℝ) - t) * M.φ t)) := by sorry

end ClarkScarf.Serial

