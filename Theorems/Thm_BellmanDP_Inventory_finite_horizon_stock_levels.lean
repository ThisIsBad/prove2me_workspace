import Mathlib
import Definitions.Def_BellmanDP_Inventory_Model

open MeasureTheory Filter Topology

namespace BellmanDP.Inventory

/-- Bellman, *Dynamic Programming*, Ch. V, § 7, Theorem 3, p. 166. Undiscounted finite process
(7.2): `f₁(x) = Min_{y ≥ x} [k(y − x) + p ∫_y^∞ (s − y) φ(s) ds]` and
`f_{n+1}(x) = Min_{y ≥ x} [k(y − x) + p ∫_y^∞ (s − y) φ(s) ds + f_n(0) ∫_y^∞ φ(s) ds
+ ∫_0^y f_n(y − s) φ(s) ds]`; in Lean `f_{n+1} = invIter k p 1 φ 0 (n + 1)` (starting from
`f₀ = 0`, discount `a = 1`). If `0 < k < p` and `φ` is a demand density, then for each
`n ≥ 1` there is a level `x̄_n ≥ 0` (here `xbar n` is the level of `f_{n+1}`, i.e. the book's
`x̄_{n+1}`) such that ordering up to `max(x, x̄_n)` attains the minimum defining `f_n(x)` for
every `x ≥ 0`, and the levels are monotone increasing in `n`. -/
theorem finite_horizon_stock_levels (k p : ℝ) (φ : ℝ → ℝ)
    (hk : 0 < k) (hkp : k < p) (hφ : DemandDensity φ) :
    ∃ xbar : ℕ → ℝ, Monotone xbar ∧ (∀ n : ℕ, 0 ≤ xbar n) ∧
      ∀ (n : ℕ) (x : ℝ), 0 ≤ x →
        IsLeast (invT k p 1 φ (invIter k p 1 φ (fun _ => 0) n) x '' Set.Ici x)
          (invT k p 1 φ (invIter k p 1 φ (fun _ => 0) n) x (max x (xbar n))) := by sorry

end BellmanDP.Inventory

