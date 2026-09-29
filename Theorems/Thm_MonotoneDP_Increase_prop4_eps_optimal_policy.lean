import Mathlib
import Definitions.Def_MonotoneDP_Increase_Model
import Definitions.Def_MonotoneDP_Increase_Assumptions

namespace MonotoneDP.Increase

/-- Bertsekas (1977), p. 450, Proposition 4: under I, I.1 and I.2 (with scalar `α`), for every
`ε > 0` there is a policy `π_ε` with `J* ≤ J_{π_ε} ≤ J* + ε e` (eq. (37)); if moreover `α < 1`,
`π_ε` can be taken stationary. -/
theorem prop4_eps_optimal_policy {S C : Type*} (m : Model S C)
    (hI : m.AssumptionI) (hI1 : m.AssumptionI1) (α : ℝ) (hI2 : m.AssumptionI2 α) :
    (∀ ε : ℝ, 0 < ε → ∃ π : m.Policy,
        m.Jstar ≤ m.Jpi π ∧ m.Jpi π ≤ fun x => m.Jstar x + (ε : EReal)) ∧
    (α < 1 → ∀ ε : ℝ, 0 < ε → ∃ μ : m.Selector,
        m.Jstar ≤ m.Jmu μ ∧ m.Jmu μ ≤ fun x => m.Jstar x + (ε : EReal)) := by sorry

end MonotoneDP.Increase
