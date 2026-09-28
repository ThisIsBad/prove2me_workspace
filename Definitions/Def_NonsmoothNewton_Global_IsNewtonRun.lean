import Mathlib
import Definitions.Def_NonsmoothNewton_Global_clarkeJac

namespace NonsmoothNewton.Global

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A run of the nonsmooth Newton iteration (3.2), `x^{k+1} = x^k - V_k^{-1} F(x^k)` with
`V_k ∈ ∂F(x^k)` (Qi–Sun 1993, p. 358): at every step `V k ∈ ∂F(x k)` and the step solves the
Newton equation `V k (x (k+1) - x k) = - F (x k)`. Every choice of `V k` is allowed. -/
def IsNewtonRun (F : E → E) (x : ℕ → E) (V : ℕ → (E →L[ℝ] E)) : Prop :=
  ∀ k, V k ∈ clarkeJac F (x k) ∧ V k (x (k + 1) - x k) = -F (x k)

end NonsmoothNewton.Global
