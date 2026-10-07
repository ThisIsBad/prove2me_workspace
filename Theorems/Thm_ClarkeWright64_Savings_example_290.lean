import Mathlib
import Definitions.Def_SupplyChainTheory_vrp
import Definitions.Def_ClarkeWright64_Savings_Instance
import Definitions.Def_ClarkeWright64_Savings_Procedure
import Definitions.Def_ClarkeWright64_Savings_TableI

namespace ClarkeWright64.Savings

/-- Clarke & Wright (1964), the numerical example, pp. 575–576: on the data of Table I with
the fleet of p. 573, every run of the procedure (every tie-break) stops with the customers
partitioned into the runs `{1,2,3,4}`, `{5}`, `{6,8,9}`, `{7,10,11,12}` and a total
distance of 290 units. -/
theorem example_290 (s : State 12) (hs : Reachable tableI s) (hterm : Terminal tableI s) :
    tableI.mileage s = 290 ∧
    (↑(s.map List.toFinset) : Multiset (Finset (Fin 13))) =
      {{1, 2, 3, 4}, {5}, {6, 8, 9}, {7, 10, 11, 12}} := by sorry

end ClarkeWright64.Savings

