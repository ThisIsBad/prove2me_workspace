import Mathlib
import Definitions.Def_ProxNewton_Exact_Basic

open scoped RealInnerProductSpace Topology
open Filter

namespace ProxNewton.Exact

/-- Lemma 2.6, arXiv:1206.1623v13, p. 8. Under the §2 standing assumptions, suppose
`H ⪰ mI` (symmetric) with `m > 0` and `∇g` is Lipschitz with constant `L1`. Let `x ∈ D`, `Δ` the
search direction (2.9), and `α ∈ (0, 1/2)`. Then every step length `t` with
`0 < t ≤ min {1, (2m/L1)(1 − α)}` satisfies the sufficient descent condition (2.19); the bound is
written division-free as `t ≤ 1 ∧ L1 * t ≤ 2m(1 − α)`. -/
theorem sufficient_descent_step {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → ℝ) (L1 m α : ℝ)
    (hg : ContDiff ℝ 1 g) (hgc : ConvexOn ℝ Set.univ g) (hL1 : 0 ≤ L1)
    (hgL : ∀ x y : EuclideanSpace ℝ (Fin n), ‖gradient g x - gradient g y‖ ≤ L1 * ‖x - y‖)
    (hD : IsProperClosedConvex D h) (hm : 0 < m) (hα : 0 < α) (hα2 : α < 1 / 2)
    (x : EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (Δ : EuclideanSpace ℝ (Fin n))
    (hx : x ∈ D) (hH : IsLowerBounded H m) (hΔ : IsSearchDirection g D h x H Δ) :
    ∀ t : ℝ, 0 < t → t ≤ 1 → L1 * t ≤ 2 * m * (1 - α) →
      SufficientDescent g D h α x Δ t := by sorry

end ProxNewton.Exact
