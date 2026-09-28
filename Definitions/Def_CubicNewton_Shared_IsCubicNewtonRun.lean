import Mathlib
import Definitions.Def_CubicNewton_Shared_IsCubicStep

namespace CubicNewton.Shared

/-- A run of the cubic regularization of Newton method (3.3) (Nesterov–Polyak 2006, p. 184) with
parameters `0 < L₀ ≤ L`, started at `x₀`: iterates `x 0 = x₀, x 1, …` (0-based, as in the paper)
and regularization parameters `M 0, M 1, …` such that at every iteration `k ≥ 0`
1. `M k ∈ [L₀, 2L]`;
2. `x (k+1)` is a global minimizer of the cubic model at `x k` with parameter `M k`, i.e. the
   paper's `T_{M_k}(x_k)` (any choice among the global minima);
3. the acceptance test `f(T_{M_k}(x_k)) ≤ f̄_{M_k}(x_k)` holds, where
   `f̄_{M_k}(x_k) = f(x_k) + min_y cubicModel = f(x_k) + cubicModel … (x k) (x (k+1))` because
   `x (k+1)` attains the minimum. -/
structure IsCubicNewtonRun {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L₀ L : ℝ) (x₀ : EuclideanSpace ℝ (Fin n)) (x : ℕ → EuclideanSpace ℝ (Fin n))
    (M : ℕ → ℝ) : Prop where
  init : x 0 = x₀
  param_mem : ∀ k, M k ∈ Set.Icc L₀ (2 * L)
  step : ∀ k, IsCubicStep g H (M k) (x k) (x (k + 1))
  accept : ∀ k, f (x (k + 1)) ≤ f (x k) + cubicModel g H (M k) (x k) (x (k + 1))

end CubicNewton.Shared
