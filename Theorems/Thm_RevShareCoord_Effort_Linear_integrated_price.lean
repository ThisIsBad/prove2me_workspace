import Mathlib
import Definitions.Def_RevShareCoord_Effort_Linear

namespace RevShareCoord.Effort.Linear

/-- Sec. 4.2.2, p. 24: the integrated channel's unique optimum is the retailer's solution with
`w = c`, `φ = 1`; its retail price is `p_I = (1 + c(1 − 2τ²))/(2(1 − τ²))`, which is increasing in
`c` if `τ < 1/√2`, decreasing if `τ > 1/√2` (and constant if `τ = 1/√2`). -/
theorem integrated_price (τ : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) :
    (∀ c : ℝ, 0 < c → c < 1 → ∀ x : ℝ × ℝ,
      (x ∈ quadrant ∧ IsMaxOn (fun y : ℝ × ℝ => channelProfit τ c y.1 y.2) quadrant x) ↔
        x = (orderQty τ 1 c, effort τ 1 (orderQty τ 1 c))) ∧
    (∀ c : ℝ, 0 < c → c < 1 →
      integratedPrice τ c = (1 + c * (1 - 2 * τ ^ 2)) / (2 * (1 - τ ^ 2))) ∧
    (τ < 1 / Real.sqrt 2 → StrictMonoOn (integratedPrice τ) (Set.Ioo 0 1)) ∧
    (τ = 1 / Real.sqrt 2 → ∀ c ∈ Set.Ioo (0 : ℝ) 1, integratedPrice τ c = 1) ∧
    (1 / Real.sqrt 2 < τ → StrictAntiOn (integratedPrice τ) (Set.Ioo 0 1)) := by sorry

end RevShareCoord.Effort.Linear

