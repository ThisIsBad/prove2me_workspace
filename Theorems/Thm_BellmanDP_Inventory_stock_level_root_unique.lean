import Mathlib
import Definitions.Def_BellmanDP_Inventory_Model

open MeasureTheory Filter Topology

namespace BellmanDP.Inventory

/-- Bellman, *Dynamic Programming*, Ch. V, § 5, Eqs. (5.3), (5.7)-(5.8), p. 161: under
hypotheses (2a)-(2d) of Theorem 1, a level `y ≥ 0` is a root of
`k = ap ∫_y^∞ φ + ak ∫_0^y φ` exactly when `∫_0^y φ(s) ds = (ap − k)/a(p − k)`, and this
equation has exactly one root `x̄ ≥ 0`. -/
theorem stock_level_root_unique (k p a : ℝ) (φ : ℝ → ℝ)
    (hk : 0 < k) (hp : 0 < p) (hφ : DemandDensity φ)
    (ha0 : 0 < a) (ha1 : a < 1) (hapk : k < a * p) :
    (∀ y : ℝ, 0 ≤ y →
      (StockLevelRoot k p a φ y ↔ (∫ s in (0 : ℝ)..y, φ s) = (a * p - k) / (a * (p - k)))) ∧
    ∃ xbar : ℝ, 0 ≤ xbar ∧ StockLevelRoot k p a φ xbar ∧
      ∀ y : ℝ, 0 ≤ y → StockLevelRoot k p a φ y → y = xbar := by sorry

end BellmanDP.Inventory

