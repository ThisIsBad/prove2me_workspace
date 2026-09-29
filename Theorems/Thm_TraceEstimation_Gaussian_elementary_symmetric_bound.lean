import Mathlib
import Definitions.Def_TraceEstimation_Gaussian_hPoly

namespace TraceEstimation.Gaussian

/-- Section 5, p. 8:8, first two displays (Avron–Toledo). (a) For non-negative reals
`x_1, …, x_n` and every `i = 1, …, n`, `∑_{S ⊆ [n], |S| = i} ∏_{j ∈ S} x_j ≤ (∑_j x_j)^i`.
(b) Consequently, for non-negative eigenvalues `λ_1, …, λ_n` with `τ = ∑ λ_j` and every
`t ≥ 0`, `|h(t)| ≤ ∑_{j=2}^n (2 τ t)^j`. -/
theorem elementary_symmetric_bound {n : ℕ} :
    (∀ x : Fin n → ℝ, (∀ j, 0 ≤ x j) → ∀ i : ℕ, 1 ≤ i → i ≤ n →
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard i, ∏ j ∈ S, x j ≤ (∑ j, x j) ^ i) ∧
    (∀ lam : Fin n → ℝ, (∀ j, 0 ≤ lam j) → ∀ t : ℝ, 0 ≤ t →
      |hPoly lam t| ≤ ∑ j ∈ Finset.Icc 2 n, (2 * (∑ k, lam k) * t) ^ j) := by sorry

end TraceEstimation.Gaussian
