import Mathlib
import Definitions.Def_SupplyChainTheory_vrp
import Definitions.Def_ClarkeWright64_Savings_Instance
import Definitions.Def_ClarkeWright64_Savings_Procedure

namespace ClarkeWright64.Savings

/-- Clarke & Wright (1964), Computational procedure, pp. 571 and 573: if `C₁ < ⋯ < C_n`,
`x₁ = ∞` and the initial allocation of one truck to each customer passes the Table II test,
then every state the procedure reaches is an allocation of the customers to runs that the
available trucks can carry. -/
theorem reachable_feasible {M n : ℕ} (I : Instance M n) (hC : StrictMono I.C)
    (hx : I.x 0 = ⊤) (hinit : I.TableIIOK ↑((init M).map I.runLoad))
    (s : State M) (hs : Reachable I s) :
    IsAllocation s ∧ I.FleetFeasible ↑(s.map I.runLoad) := by sorry

end ClarkeWright64.Savings

