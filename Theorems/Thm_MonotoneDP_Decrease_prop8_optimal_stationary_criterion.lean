import Mathlib
import Definitions.Def_MonotoneDP_Decrease_Model
import Definitions.Def_MonotoneDP_Decrease_Assumptions

namespace MonotoneDP.Decrease

/-- Bertsekas (1977), p. 455, Proposition 8: under D and D.1, a stationary policy
`{μ*, μ*, …}` is optimal (`J_{μ*} = J*`) if and only if (48) `T_{μ*}(J_{μ*}) = T(J_{μ*})`. -/
theorem prop8_optimal_stationary_criterion {S C : Type*} (m : Model S C)
    (hD : m.AssumptionD) (hD1 : m.AssumptionD1) (μ : m.Selector) :
    m.Jmu μ = m.Jstar ↔ m.Tmu μ (m.Jmu μ) = m.T (m.Jmu μ) := by sorry

end MonotoneDP.Decrease
