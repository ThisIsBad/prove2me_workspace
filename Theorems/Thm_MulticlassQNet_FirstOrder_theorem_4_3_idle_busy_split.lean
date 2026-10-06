import Mathlib
import Definitions.Def_MulticlassQNet_FirstOrder_Network
import Definitions.Def_MulticlassQNet_FirstOrder_Dynamics
import Definitions.Def_MulticlassQNet_FirstOrder_Constraints

namespace MulticlassQNet.FirstOrder

/-- Theorem 4.3 (p. 20): for each station `i` and class `r'`,
`∑_{r ∈ C_i} I_{rr'} + N_{ir'} = λ_{r'} x_{r'}` (= `n̄_{r'}`). -/
theorem theorem_4_3_idle_busy_split {N R : ℕ} (net : Network N R) (lam : Fin R → ℝ)
    (htraffic : net.IsTrafficSolution lam) (hopen : net.IsOpen) (hload : net.LoadLtOne lam)
    (P : Policy net) (π : (Fin R → ℕ) → ℝ) (hA : P.AssumptionA π) :
    net.Eq28 (meanNum π) (P.busyMoment π) (P.idleMoment π) := by sorry

end MulticlassQNet.FirstOrder

