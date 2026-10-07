import Mathlib
import Definitions.Def_BalasAdditive_Convergence_Algorithm

set_option autoImplicit false

namespace BalasAdditive.Convergence

/-- Remark after (16), p. 524: the improving set `N_p` formed for a feasible
generated solution `u^p` is empty. -/
theorem feasible_solution_no_improving {n m : ℕ} (P : Problem n m) (σ : State n)
    (hr : Reachable P σ) (p : ℕ) (hp : p < σ.history.length)
    (hfeas : P.lp.Feasible (σ.J p)) :
    σ.N p = ∅ := by sorry

end BalasAdditive.Convergence

