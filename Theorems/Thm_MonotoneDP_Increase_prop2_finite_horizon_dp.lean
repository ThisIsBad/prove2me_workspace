import Mathlib
import Definitions.Def_MonotoneDP_Increase_Model
import Definitions.Def_MonotoneDP_Increase_Assumptions

namespace MonotoneDP.Increase

/-- Bertsekas (1977), p. 448, Proposition 2: under Assumptions I and I.2, the optimal value
function of the `N`-stage problem (36) equals `T^N(J̄)` for all `N = 1, 2, …`. -/
theorem prop2_finite_horizon_dp {S C : Type*} (m : Model S C)
    (hI : m.AssumptionI) (hI2 : ∃ α : ℝ, m.AssumptionI2 α) :
    ∀ N : ℕ, 1 ≤ N → m.JN N = (m.T)^[N] m.Jbar := by sorry

end MonotoneDP.Increase
