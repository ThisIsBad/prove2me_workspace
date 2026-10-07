import Mathlib
import Definitions.Def_RobinsonFP_Convergence_VectorSystem

namespace RobinsonFP.Convergence

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Robinson (1951), p. 296, inequality (1): for all probability vectors `x` (over rows) and `y`
(over columns), `min_j Σ_i a_ij x_i ≤ max_i Σ_j a_ij y_j`. -/
theorem ineq1 [Nonempty ι] [Nonempty κ] (A : Matrix ι κ ℝ) :
    ∀ x ∈ stdSimplex ℝ ι, ∀ y ∈ stdSimplex ℝ κ,
      vmin (fun j => ∑ i, A i j * x i) ≤ vmax (fun i => ∑ j, A i j * y j) := by sorry

end RobinsonFP.Convergence

