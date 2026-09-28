import Mathlib
import Definitions.Def_CubicNewton_Shared_IsCubicStep

namespace CubicNewton.LocalQuad

/-- A run of the relaxed cubic regularization of Newton method (3.5) (Nesterov–Polyak 2006,
Section 3, p. 186): iterates `x 0, x 1, …` (0-based, as in the paper; `x 0` is the starting point)
and parameters `M 0, M 1, …` such that for every `k ≥ 0`
1. `M k ∈ (0, 2L]`;
2. `x (k+1) = T_{M k}(x k)` is a global minimizer of the cubic model at `x k` with parameter
   `M k` (any choice among the global minima).
Unlike method (3.3) there is no lower bound `L₀` on `M k` and no acceptance test. -/
def IsRelaxedRun {n : ℕ} (L : ℝ) (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (M : ℕ → ℝ) : Prop :=
  ∀ k, M k ∈ Set.Ioc 0 (2 * L) ∧ CubicNewton.Shared.IsCubicStep g H (M k) (x k) (x (k + 1))

end CubicNewton.LocalQuad
