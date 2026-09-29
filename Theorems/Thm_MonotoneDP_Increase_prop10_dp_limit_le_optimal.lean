import Mathlib
import Definitions.Def_MonotoneDP_Increase_Model
import Definitions.Def_MonotoneDP_Increase_Assumptions

namespace MonotoneDP.Increase

/-- Bertsekas (1977), p. 456, Proposition 10: under I, I.1 and I.2,
`J_∞ ≤ T(J_∞) ≤ T(J*) = J*` (eq. (50)); and `J_∞ = T(J_∞) = T(J*) = J*` (eq. (51)) holds iff
`J_∞ = T(J_∞)` (eq. (52)). -/
theorem prop10_dp_limit_le_optimal {S C : Type*} (m : Model S C)
    (hI : m.AssumptionI) (hI1 : m.AssumptionI1) (hI2 : ∃ α : ℝ, m.AssumptionI2 α) :
    (m.Jinf ≤ m.T m.Jinf ∧ m.T m.Jinf ≤ m.T m.Jstar ∧ m.T m.Jstar = m.Jstar) ∧
      ((m.Jinf = m.T m.Jinf ∧ m.T m.Jinf = m.T m.Jstar ∧ m.T m.Jstar = m.Jstar) ↔
        m.Jinf = m.T m.Jinf) := by sorry

end MonotoneDP.Increase
