import Mathlib
import Definitions.Def_BellmanDP_Inventory_Model

open MeasureTheory Filter Topology

namespace BellmanDP.Inventory

/-- Bellman, *Dynamic Programming*, Ch. V, § 5, Theorem 1, pp. 159-160, with (4b) corrected to
`y = x`. Let `k, p > 0`, `0 < a < 1` and let `φ` be a demand density (positive on `(0, ∞)`,
total mass 1, finite mean). Equation (5.1), `f(x) = Min_{y ≥ x} T(y, x, f)`, has exactly one
solution among measurable functions bounded on `[0, ∞)`, and:
* if `ap > k`, the equation `k = ap ∫_y^∞ φ + ak ∫_0^y φ` has exactly one root `x̄ ≥ 0`, and
  for every `x ≥ 0` the minimum is attained at `y = x̄` when `x ≤ x̄` and at `y = x` when
  `x ≥ x̄` (order up to `x̄`);
* if `ap ≤ k`, the minimum is attained at `y = x` for every `x ≥ 0` (never order). -/
theorem constant_stock_level_optimal (k p a : ℝ) (φ : ℝ → ℝ)
    (hk : 0 < k) (hp : 0 < p) (hφ : DemandDensity φ) (ha0 : 0 < a) (ha1 : a < 1) :
    (k < a * p →
      ∃ xbar : ℝ, 0 ≤ xbar ∧ StockLevelRoot k p a φ xbar ∧
        (∀ y : ℝ, 0 ≤ y → StockLevelRoot k p a φ y → y = xbar) ∧
        ∃ f : ℝ → ℝ, BoundedClass f ∧ SolvesInf (invT k p a φ) f ∧
          (∀ g : ℝ → ℝ, BoundedClass g → SolvesInf (invT k p a φ) g →
            Set.EqOn g f (Set.Ici 0)) ∧
          ∀ x : ℝ, 0 ≤ x →
            IsLeast (invT k p a φ f x '' Set.Ici x) (invT k p a φ f x (max x xbar))) ∧
    (a * p ≤ k →
      ∃ f : ℝ → ℝ, BoundedClass f ∧ SolvesInf (invT k p a φ) f ∧
        (∀ g : ℝ → ℝ, BoundedClass g → SolvesInf (invT k p a φ) g →
          Set.EqOn g f (Set.Ici 0)) ∧
        ∀ x : ℝ, 0 ≤ x → IsLeast (invT k p a φ f x '' Set.Ici x) (invT k p a φ f x x)) := by sorry

end BellmanDP.Inventory

