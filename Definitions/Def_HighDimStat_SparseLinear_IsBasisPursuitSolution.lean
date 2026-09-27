import Mathlib
import Definitions.Def_HighDimStat_SparseLinear_L1Norm

namespace HighDimStat.SparseLinear

/-- `θhat` is an optimal solution of the basis pursuit linear program (7.9),
`min_θ ‖θ‖₁` s.t. `Xθ = y`, of Wainwright, *High-Dimensional Statistics* (2019), p. 200:
`θhat` is feasible and minimizes the `ℓ¹`-norm among all feasible vectors. -/
def IsBasisPursuitSolution {n d : ℕ} (X : Matrix (Fin n) (Fin d) ℝ) (y : Fin n → ℝ)
    (θhat : Fin d → ℝ) : Prop :=
  X.mulVec θhat = y ∧ ∀ β : Fin d → ℝ, X.mulVec β = y → l1Norm θhat ≤ l1Norm β

end HighDimStat.SparseLinear
