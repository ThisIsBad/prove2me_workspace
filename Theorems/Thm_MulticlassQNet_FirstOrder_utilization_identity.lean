import Mathlib
import Definitions.Def_MulticlassQNet_FirstOrder_Network
import Definitions.Def_MulticlassQNet_FirstOrder_Dynamics

namespace MulticlassQNet.FirstOrder

/-- Utilization identity (§4.2, proof of Theorem 4.2, p. 19): in steady state
`E[1{B_r}] = λ_r / μ_r`, where `λ` solves the traffic equations (15). -/
theorem utilization_identity {N R : ℕ} (net : Network N R) (lam : Fin R → ℝ)
    (htraffic : net.IsTrafficSolution lam) (hopen : net.IsOpen) (hload : net.LoadLtOne lam)
    (P : Policy net) (π : (Fin R → ℕ) → ℝ) (hA : P.AssumptionA π) :
    ∀ r, P.busyProb π r = lam r / net.μ r := by sorry

end MulticlassQNet.FirstOrder

