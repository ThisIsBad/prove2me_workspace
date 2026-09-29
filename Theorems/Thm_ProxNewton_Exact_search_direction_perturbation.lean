import Mathlib
import Definitions.Def_ProxNewton_Exact_Basic

open scoped RealInnerProductSpace Topology
open Filter

namespace ProxNewton.Exact

/-- Proposition 3.6, arXiv:1206.1623v13, p. 13 (reading `m₁ = m`). For all constants
`0 < m ≤ M` and `0 < m2 ≤ M2` there is `θ > 0`, depending only on `m, M, m2, M2`, such that
whenever `h` is proper closed convex with domain `D`, `mI ⪯ H1 ⪯ MI`, `m2 I ⪯ H2 ⪯ M2 I`
(symmetric), and `Δ1`, `Δ2` are the search directions (2.9) at the same point `x` with `H1` and
`H2`, then `‖Δ1 − Δ2‖ ≤ √((1 + θ)/m) · ‖(H2 − H1)Δ1‖^(1/2) · ‖Δ1‖^(1/2)`. -/
theorem search_direction_perturbation (m M m2 M2 : ℝ)
    (hm : 0 < m) (hmM : m ≤ M) (hm2 : 0 < m2) (hmM2 : m2 ≤ M2) :
    ∃ θ : ℝ, 0 < θ ∧
      ∀ (n : ℕ) (g : EuclideanSpace ℝ (Fin n) → ℝ) (D : Set (EuclideanSpace ℝ (Fin n)))
        (h : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
        (H1 H2 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        (Δ1 Δ2 : EuclideanSpace ℝ (Fin n)),
        IsProperClosedConvex D h →
        IsBoundedBetween H1 m M → IsBoundedBetween H2 m2 M2 →
        IsSearchDirection g D h x H1 Δ1 → IsSearchDirection g D h x H2 Δ2 →
        ‖Δ1 - Δ2‖ ≤
          Real.sqrt ((1 + θ) / m) * Real.sqrt ‖(H2 - H1) Δ1‖ * Real.sqrt ‖Δ1‖ := by sorry

end ProxNewton.Exact
