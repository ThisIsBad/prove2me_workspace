import Mathlib
import Definitions.Def_HighDimStat_SparseLinear_L1Norm

namespace HighDimStat.SparseLinear

/-- `θhat` is an optimal solution of the Lagrangian Lasso program (7.18),
`argmin_θ (1/(2n))‖y − Xθ‖₂² + λₙ‖θ‖₁`, of Wainwright, *High-Dimensional Statistics* (2019),
p. 206: `θhat` attains the minimum of the Lagrangian objective over all of `ℝ^d`. -/
def IsLagrangianLassoSolution {n d : ℕ} (X : Matrix (Fin n) (Fin d) ℝ) (y : Fin n → ℝ)
    (lam : ℝ) (θhat : Fin d → ℝ) : Prop :=
  ∀ β : Fin d → ℝ,
    (1 / (2 * (n : ℝ))) * (∑ i, (y i - X.mulVec θhat i) ^ 2) + lam * l1Norm θhat ≤
    (1 / (2 * (n : ℝ))) * (∑ i, (y i - X.mulVec β i) ^ 2) + lam * l1Norm β

end HighDimStat.SparseLinear
