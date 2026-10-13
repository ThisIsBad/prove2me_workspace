import Mathlib
import Definitions.Def_MonotoneDP_Increase_Model
import Definitions.Def_MonotoneDP_Increase_Assumptions

namespace BertsekasShreve.Monotone

/-- Bertsekas & Shreve (1996), p. 78, Proposition 5.4: let I, I.1 and I.2 hold. A stationary policy
`(μ*, μ*, …)` is optimal (`J_{μ*} = J*`) if and only if `T_{μ*}(J*) = T(J*)` (eq. (18)).
Furthermore, if for each `x ∈ S` there exists a policy which is optimal at `x`
(`J_π(x) = J*(x)`), then there exists a stationary optimal policy. -/
theorem prop5_4_optimal_stationary_criterion {S C : Type*} (m : MonotoneDP.Increase.Model S C)
    (hI : m.AssumptionI) (hI1 : m.AssumptionI1) (hI2 : ∃ α : ℝ, m.AssumptionI2 α) :
    (∀ μ : m.Selector, m.Jmu μ = m.Jstar ↔ m.Tmu μ m.Jstar = m.T m.Jstar) ∧
      ((∀ x : S, ∃ π : m.Policy, m.Jpi π x = m.Jstar x) →
        ∃ μ : m.Selector, m.Jmu μ = m.Jstar) := by sorry

end BertsekasShreve.Monotone

