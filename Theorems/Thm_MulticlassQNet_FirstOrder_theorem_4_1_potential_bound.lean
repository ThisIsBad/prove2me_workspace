import Mathlib
import Definitions.Def_MulticlassQNet_FirstOrder_Network
import Definitions.Def_MulticlassQNet_FirstOrder_Dynamics
import Definitions.Def_MulticlassQNet_FirstOrder_Constraints

namespace MulticlassQNet.FirstOrder

/-- Theorem 4.1 (p. 14): for any class set `S`, any f-parameters satisfying (17) (and `f ≥ 0`
on `S`, p. 9), and any policy satisfying Assumption A,
`N'(S) ≤ D'(S) · ∑_{r∈S} f(r) λ_r x_r`, i.e. (18) multiplied by `D'(S)`. -/
theorem theorem_4_1_potential_bound {N R : ℕ} (net : Network N R) (lam : Fin R → ℝ)
    (htraffic : net.IsTrafficSolution lam) (hopen : net.IsOpen) (hload : net.LoadLtOne lam)
    (P : Policy net) (π : (Fin R → ℕ) → ℝ) (hA : P.AssumptionA π)
    (S : Finset (Fin R)) (f : Fin R → ℝ) (fi : Fin N → ℝ)
    (h17 : net.FCondition S f fi) (hf : ∀ r ∈ S, 0 ≤ f r) :
    net.Nprime lam S f ≤ net.Dprime S f fi * ∑ r ∈ S, f r * meanNum π r := by sorry

end MulticlassQNet.FirstOrder

