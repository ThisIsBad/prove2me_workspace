import Mathlib
import Definitions.Def_SupplyChainTheory_vrp
import Definitions.Def_ClarkeWright64_Savings_Instance
import Definitions.Def_ClarkeWright64_Savings_Procedure

namespace ClarkeWright64.Savings

/-- Clarke & Wright (1964), Computational procedure, relation (A), p. 573: the initial basic
solution has `t_{y,0} = 2` for every customer, and at every state the procedure reaches, every
customer `P_y` has `∑_{z ≠ y} t_{y,z} = 2` (the sum includes `z = 0`). -/
theorem relation_A {M n : ℕ} (I : Instance M n) :
    (∀ y : Fin (M + 1), y ≠ 0 → t (init M) y 0 = 2) ∧
    ∀ s : State M, Reachable I s →
      ∀ y : Fin (M + 1), y ≠ 0 → ∑ z ∈ Finset.univ.erase y, t s y z = 2 := by sorry

end ClarkeWright64.Savings

