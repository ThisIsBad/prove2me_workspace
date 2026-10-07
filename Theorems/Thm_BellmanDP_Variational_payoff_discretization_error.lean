import Mathlib
import Definitions.Def_BellmanDP_Variational_Approximation

namespace BellmanDP.Variational

open Set

/-- Bellman, *Dynamic Programming*, Ch. IX, § 12, proof of Theorem 2, Eq. (12.13), p. 262: under the
assumptions (11) on `F (x, y)`, `G (x, y)`, for `c > 0` and `T > 0` there is a constant `B′`
(depending only on `c, T, F, G`) such that for every `n ≥ 1` and every step control
`φ (t) = φ_k` on `k/n ≤ t < (k+1)/n` with `0 ≤ φ_k ≤ 1`,
`|J (φ) − J_N ({φ_k}, n)| ≤ B′ / n`, where `J (φ) = ∫_0^T F (x, φ x) dt` along the solution of
`dx/dt = G (x, φ x)`, `x (0) = c`, and `N = ⌊T n⌋`. -/
theorem payoff_discretization_error (F G : ℝ → ℝ → ℝ) (hFG : Assumptions11 F G)
    (c T : ℝ) (hc : 0 < c) (hT : 0 < T) :
    ∃ B : ℝ, ∀ n : ℕ, 0 < n → ∀ (φs : ℕ → ℝ) (x : ℝ → ℝ),
      (∀ k ≤ horizonSteps T n, φs k ∈ Icc (0 : ℝ) 1) →
      IsTrajectory (phiForm G) c (stepControl n φs) T x →
      |(∫ t in (0 : ℝ)..T, phiForm F (x t) (stepControl n φs t)) -
          discretePayoff (phiForm F) (phiForm G) c n φs (horizonSteps T n)| ≤ B / n := by sorry

end BellmanDP.Variational

