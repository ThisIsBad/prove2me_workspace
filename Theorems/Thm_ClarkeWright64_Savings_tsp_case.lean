import Mathlib
import Definitions.Def_SupplyChainTheory_vrp
import Definitions.Def_ClarkeWright64_Savings_Instance
import Definitions.Def_ClarkeWright64_Savings_Procedure

namespace ClarkeWright64.Savings

/-- Clarke & Wright (1964), Formulation, p. 569: if the distances are shortest-route distances
(a metric) and the largest capacity `C_n` is at least the total load of all customers, with at
least one such truck available, the optimum of the problem equals the length of an optimal
traveling salesman tour through the depot and all customers. -/
theorem tsp_case {M n : ℕ} (I : Instance M n) (hd : SupplyChainTheory.VRPMetric I.d)
    (hcap : ∑ j ∈ Finset.univ.erase (0 : Fin (M + 1)), I.q j ≤ I.C (Fin.last n))
    (htruck : 1 ≤ I.x (Fin.last n)) :
    optMileage I = SupplyChainTheory.tspOpt I.d := by sorry

end ClarkeWright64.Savings

