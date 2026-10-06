import Mathlib
import Definitions.Def_MulticlassQNet_FirstOrder_Network
import Definitions.Def_MulticlassQNet_FirstOrder_Dynamics
import Definitions.Def_MulticlassQNet_FirstOrder_Constraints

namespace MulticlassQNet.FirstOrder

/-- Theorem 4.2 (p. 18): for every policy satisfying Assumption A, the moments
`I_{rr'} = E[1{B_r} n_{r'}]` and `n̄_r = λ_r x_r` satisfy (24) and (25). -/
theorem theorem_4_2_second_moment_equalities {N R : ℕ} (net : Network N R) (lam : Fin R → ℝ)
    (htraffic : net.IsTrafficSolution lam) (hopen : net.IsOpen) (hload : net.LoadLtOne lam)
    (P : Policy net) (π : (Fin R → ℕ) → ℝ) (hA : P.AssumptionA π) :
    net.Eq24 lam (meanNum π) (P.busyMoment π) ∧
      net.Eq25 lam (meanNum π) (P.busyMoment π) := by sorry

end MulticlassQNet.FirstOrder

