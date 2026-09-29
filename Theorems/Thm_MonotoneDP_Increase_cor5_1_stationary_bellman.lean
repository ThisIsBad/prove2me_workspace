import Mathlib
import Definitions.Def_MonotoneDP_Increase_Model
import Definitions.Def_MonotoneDP_Increase_Assumptions

namespace MonotoneDP.Increase

/-- Bertsekas (1977), p. 453, Corollary 5.1: under I, I.1 and I.2, for every stationary policy
`{μ, μ, …}`, `J_μ = T_μ(J_μ)`; moreover every `J' ∈ F` with `J' ≥ J̄` and `J' ≥ T_μ(J')`
satisfies `J' ≥ J_μ`. -/
theorem cor5_1_stationary_bellman {S C : Type*} (m : Model S C)
    (hI : m.AssumptionI) (hI1 : m.AssumptionI1) (hI2 : ∃ α : ℝ, m.AssumptionI2 α) :
    ∀ μ : m.Selector, m.Jmu μ = m.Tmu μ (m.Jmu μ) ∧
      ∀ J' : S → EReal, m.Jbar ≤ J' → m.Tmu μ J' ≤ J' → m.Jmu μ ≤ J' := by sorry

end MonotoneDP.Increase
