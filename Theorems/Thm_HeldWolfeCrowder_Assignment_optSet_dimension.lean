import Mathlib
import Definitions.Def_HeldWolfeCrowder_Assignment_Setting

namespace HeldWolfeCrowder.Assignment

/-- Held–Wolfe–Crowder (1974), p. 70, **Theorem 3.1**: if an assignment problem of order `n` has
a unique optimal one-to-one assignment, then the optimal set of its dual problem (3.3),
`max w`, has dimension `n` (the dimension of its affine hull). -/
theorem optSet_dimension {n : ℕ} (a : Matrix (Fin n) (Fin n) ℝ)
    (huniq : ∃! σ : Equiv.Perm (Fin n), IsOptimalAssignment a σ) :
    Module.finrank ℝ (vectorSpan ℝ (optSet a)) = n := by sorry

end HeldWolfeCrowder.Assignment

