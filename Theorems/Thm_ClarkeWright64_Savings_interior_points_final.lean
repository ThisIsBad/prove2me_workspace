import Mathlib
import Definitions.Def_SupplyChainTheory_vrp
import Definitions.Def_ClarkeWright64_Savings_Instance
import Definitions.Def_ClarkeWright64_Savings_Procedure

namespace ClarkeWright64.Savings

/-- Clarke & Wright (1964), Theoretical aspects, pp. 571–572: in a step of the procedure from a
reachable state, (a) every link between two customers survives, (b) no `t_{y,0}` increases, and
(c) a customer with `t_{y,0} = 0` (linked to two customers) lies in no admissible cell of any
later state, so it is never considered again for linking. -/
theorem interior_points_final {M n : ℕ} (I : Instance M n) (s s' : State M)
    (hs : Reachable I s) (hstep : Step I s s') :
    (∀ y z : Fin (M + 1), y ≠ 0 → z ≠ 0 → t s y z = 1 → t s' y z = 1) ∧
    (∀ y : Fin (M + 1), y ≠ 0 → t s' y 0 ≤ t s y 0) ∧
    (∀ y : Fin (M + 1), y ≠ 0 → t s y 0 = 0 →
      ∀ s'' : State M, Relation.ReflTransGen (Step I) s s'' →
        ∀ z : Fin (M + 1), ¬ Admissible I s'' y z ∧ ¬ Admissible I s'' z y) := by sorry

end ClarkeWright64.Savings

