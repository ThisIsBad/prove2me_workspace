import Mathlib
import Definitions.Def_VanderbeiLP_CentralPath_BarrierProblem

open Matrix Filter Topology

namespace VanderbeiLP.CentralPath

/-- Exercise 10.7 (p. 150). If the LP `maximize cᵀx s.t. Ax ≤ b, x ≥ 0` has feasible solutions and
its set of feasible solutions is bounded, then there is a strictly positive dual feasible solution:
`Aᵀy − z = c` with `y > 0` and `z > 0`. -/
theorem dual_strictly_feasible_of_bounded {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (hne : (primalFeasibleSet A b).Nonempty)
    (hbdd : Bornology.IsBounded (primalFeasibleSet A b)) :
    DualStrictlyFeasible A c := by sorry

end VanderbeiLP.CentralPath

