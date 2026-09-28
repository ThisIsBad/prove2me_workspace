import Mathlib
import Definitions.Def_CubicNewton_Shared_IsCubicNewtonRun

namespace CubicNewton.StarConvex

/-- Nesterov–Polyak 2006, Section 3, p. 184 (remark after method (3.3)): since `f̄_M(x) ≤ f(x)`,
every run of the cubic regularization of Newton method (3.3) is monotone,
`f(x_{k+1}) ≤ f(x_k)` for all `k ≥ 0`. -/
theorem run_monotone {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L₀ L : ℝ) (x₀ : EuclideanSpace ℝ (Fin n)) (x : ℕ → EuclideanSpace ℝ (Fin n))
    (M : ℕ → ℝ) (hrun : CubicNewton.Shared.IsCubicNewtonRun f g H L₀ L x₀ x M) :
    ∀ k, f (x (k + 1)) ≤ f (x k) := by sorry

end CubicNewton.StarConvex

