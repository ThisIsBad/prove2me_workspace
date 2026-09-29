import Mathlib
import Definitions.Def_MonotoneDP_Increase_Model
import Definitions.Def_MonotoneDP_Increase_Assumptions

namespace MonotoneDP.Increase

/-- Bertsekas (1977), p. 455, Proposition 7: under I, I.1 and I.2, a stationary policy
`{μ*, μ*, …}` is optimal iff `T_{μ*}(J*) = T(J*)` (eq. (47)); moreover, if there exists an optimal
policy, there exists an optimal stationary policy. -/
theorem prop7_optimal_stationary_criterion {S C : Type*} (m : Model S C)
    (hI : m.AssumptionI) (hI1 : m.AssumptionI1) (hI2 : ∃ α : ℝ, m.AssumptionI2 α) :
    (∀ μ : m.Selector, m.Jmu μ = m.Jstar ↔ m.Tmu μ m.Jstar = m.T m.Jstar) ∧
      ((∃ π : m.Policy, m.Jpi π = m.Jstar) → ∃ μ : m.Selector, m.Jmu μ = m.Jstar) := by sorry

end MonotoneDP.Increase
