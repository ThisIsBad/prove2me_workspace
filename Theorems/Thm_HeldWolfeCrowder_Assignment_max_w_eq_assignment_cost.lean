import Mathlib
import Definitions.Def_HeldWolfeCrowder_Assignment_Setting

namespace HeldWolfeCrowder.Assignment

/-- Held–Wolfe–Crowder (1974), §3, p. 69, Eqs. (3.1)–(3.3): the optimal value of the assignment
problem is that of the dual (3.2), whose objective maximized over `ρ` is `w` of (3.3). So `w`
attains its maximum, and its maximum value is the cost of an optimal one-to-one assignment. -/
theorem max_w_eq_assignment_cost {n : ℕ} (a : Matrix (Fin n) (Fin n) ℝ)
    (σ : Equiv.Perm (Fin n)) (hσ : IsOptimalAssignment a σ) :
    IsGreatest (Set.range (w a)) (assignCost a σ) := by sorry

end HeldWolfeCrowder.Assignment

