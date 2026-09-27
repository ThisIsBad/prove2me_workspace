import Mathlib

namespace HighDimProb.Appetizer

/-- **Theorem 0.0.2** (Approximate Carathéodory's theorem), Vershynin,
*High-Dimensional Probability* (2018), p. 2.

Consider a set `T ⊆ ℝⁿ` whose diameter is bounded by `1` (so `T` is bounded and
`diam T ≤ 1`; Mathlib's `Metric.diam` is `0` on unbounded sets, hence the explicit
boundedness hypothesis). Then, for every point
`x ∈ conv(T)` and every positive integer `k`, one can find points
`x₁, …, x_k ∈ T` such that `‖x − (1/k) ∑ⱼ xⱼ‖₂ ≤ 1/√k`. -/
theorem approx_caratheodory {n : ℕ} (T : Set (EuclideanSpace ℝ (Fin n)))
    (hTb : Bornology.IsBounded T) (hT : Metric.diam T ≤ 1)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ convexHull ℝ T)
    (k : ℕ) (hk : 0 < k) :
    ∃ x' : Fin k → EuclideanSpace ℝ (Fin n), (∀ j, x' j ∈ T) ∧
      ‖x - (k : ℝ)⁻¹ • ∑ j, x' j‖ ≤ 1 / Real.sqrt k := by sorry

end HighDimProb.Appetizer
