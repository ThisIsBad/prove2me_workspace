import Mathlib
import Definitions.Def_HeldWolfeCrowder_Assignment_Setting

namespace MunkresAlg.Assignment

/-- Munkres (1957), §1, Remark (2), p. 33: subtracting arbitrary row constants `u i` and column
constants `v j` from the matrix does not change the set of optimal assignments. -/
theorem remark_2_reduction {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (u v : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) :
    HeldWolfeCrowder.Assignment.IsOptimalAssignment A σ ↔
      HeldWolfeCrowder.Assignment.IsOptimalAssignment (fun i j => A i j - u i - v j) σ := by sorry

end MunkresAlg.Assignment

