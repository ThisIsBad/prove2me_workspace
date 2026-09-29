import Mathlib
import Definitions.Def_MonotoneDP_Decrease_Model
import Definitions.Def_MonotoneDP_Decrease_Assumptions

namespace MonotoneDP.Decrease

/-- Bertsekas (1977), p. 454, Corollary 6.2: under D and D.1, for every stationary policy
`{μ, μ, …}`, `J_μ = T_μ(J_μ)`; moreover every `J' ∈ F` with `J' ≤ J̄` and `J' ≤ T_μ(J')`
satisfies `J' ≤ J_μ`. -/
theorem cor6_2_stationary_bellman {S C : Type*} (m : Model S C)
    (hD : m.AssumptionD) (hD1 : m.AssumptionD1) (μ : m.Selector) :
    m.Jmu μ = m.Tmu μ (m.Jmu μ) ∧
      ∀ J' : S → EReal, J' ≤ m.Jbar → J' ≤ m.Tmu μ J' → J' ≤ m.Jmu μ := by sorry

end MonotoneDP.Decrease
