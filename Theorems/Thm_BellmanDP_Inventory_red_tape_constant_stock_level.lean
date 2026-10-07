import Mathlib
import Definitions.Def_BellmanDP_Inventory_Model

open MeasureTheory Filter Topology

namespace BellmanDP.Inventory

/-- Bellman, *Dynamic Programming*, Ch. V, § 9, Theorem 4, p. 171. Under the assumptions of
Theorem 1 on `a, k, p, φ` and `q ≥ 0`, suppose `x̄ ≥ 0` is an absolute minimizer of
`ψ(y) = ky + a [∫_y^∞ [p(s − y) + q] φ(s) ds − k ∫_0^y (y − s) φ(s) ds]` on `[0, ∞)` and that
`ψ` has no later minimum (it is monotone nondecreasing on `[x̄, ∞)`; this is the reading of
"the last minimum of ψ is the absolute minimum"). Then equation (9.1) has exactly one solution
in the class of measurable functions bounded on `[0, ∞)`, and for every `x ≥ 0` its minimum is
attained at `y = x̄` if `x ≤ x̄` and at `y = x` if `x ≥ x̄`. -/
theorem red_tape_constant_stock_level (k p q a : ℝ) (φ : ℝ → ℝ)
    (hk : 0 < k) (hp : 0 < p) (hq : 0 ≤ q) (hφ : DemandDensity φ)
    (ha0 : 0 < a) (ha1 : a < 1) (hapk : k < a * p)
    (xbar : ℝ) (hxbar : 0 ≤ xbar)
    (hmin : ∀ y : ℝ, 0 ≤ y → psiQ k p q a φ xbar ≤ psiQ k p q a φ y)
    (hlast : MonotoneOn (psiQ k p q a φ) (Set.Ici xbar)) :
    ∃ f : ℝ → ℝ, BoundedClass f ∧ SolvesInf (invTq k p q a φ) f ∧
      (∀ g : ℝ → ℝ, BoundedClass g → SolvesInf (invTq k p q a φ) g →
        Set.EqOn g f (Set.Ici 0)) ∧
      ∀ x : ℝ, 0 ≤ x →
        IsLeast (invTq k p q a φ f x '' Set.Ici x) (invTq k p q a φ f x (max x xbar)) := by sorry

end BellmanDP.Inventory

