import Mathlib
import Definitions.Def_MonotoneDP_Increase_Model
import Definitions.Def_MonotoneDP_Increase_Assumptions

namespace MonotoneDP.Increase

/-- Bertsekas (1977), p. 451, Proposition 5: under I, I.1 and I.2, `J* = T(J*)`; moreover every
`J' ∈ F` with `J' ≥ J̄` and `J' ≥ T(J')` satisfies `J' ≥ J*`. -/
theorem prop5_bellman_equation {S C : Type*} (m : Model S C)
    (hI : m.AssumptionI) (hI1 : m.AssumptionI1) (hI2 : ∃ α : ℝ, m.AssumptionI2 α) :
    m.Jstar = m.T m.Jstar ∧
      ∀ J' : S → EReal, m.Jbar ≤ J' → m.T J' ≤ J' → m.Jstar ≤ J' := by sorry

end MonotoneDP.Increase
