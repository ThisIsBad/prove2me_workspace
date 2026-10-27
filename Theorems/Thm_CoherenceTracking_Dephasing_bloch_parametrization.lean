import Mathlib
import Definitions.Def_CoherenceTracking_Dephasing_Model

namespace CoherenceTracking.Dephasing
theorem bloch_parametrization :
    (∀ ρ : Qmat, IsQubitState ρ →
        blochState (blochVec ρ) = ρ ∧ coherence ρ = 4 * Complex.normSq (ρ 0 1)) ∧
    (∀ v : BVec, blochVec (blochState v) = v) ∧
    (∀ v : BVec, IsQubitState (blochState v) ↔ ∑ α, v α ^ 2 ≤ 1) := by sorry
end CoherenceTracking.Dephasing

