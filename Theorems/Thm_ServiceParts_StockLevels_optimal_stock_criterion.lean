import Mathlib
import Definitions.Def_ServiceParts_StockLevels_Basic
import Definitions.Def_ServiceParts_StockLevels_CompoundPoissonDemand
import Definitions.Def_ServiceParts_StockLevels_Problems

namespace ServiceParts.StockLevels

theorem optimal_stock_criterion (d : CompoundPoissonDemand) (c θ : ℝ) (hc : 0 < c)
    (hθ : 0 < θ) :
    (∀ s, 0 ≤ fdiff2 (relaxedCost d c θ) s) ∧
    (∀ s, fdiff (relaxedCost d c θ) s = -(1 + θ * c) * (1 - d.readyRate s) + θ * c) ∧
    (∀ s, 0 ≤ fdiff (relaxedCost d c θ) s ↔ s ∈ stockSet d c θ) ∧
    (stockSet d c θ).Nonempty ∧
    ∀ sStar : ℕ, IsLeast (stockSet d c θ) sStar →
      (∀ s, relaxedCost d c θ sStar ≤ relaxedCost d c θ s) ∧
      (∀ s, s < sStar → relaxedCost d c θ sStar < relaxedCost d c θ s) := by sorry

end ServiceParts.StockLevels

