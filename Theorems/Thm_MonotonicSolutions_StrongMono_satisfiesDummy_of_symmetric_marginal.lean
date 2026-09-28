import Mathlib
import Definitions.Def_MonotonicSolutions_StrongMono_Game
import Definitions.Def_MonotonicSolutions_StrongMono_Axioms

namespace MonotonicSolutions.StrongMono

/-- Eq. (8) of Young (1985, p. 70): for a symmetric allocation procedure `φ` satisfying (7),
dummy players get nothing: for every game `v` and player `i`, `v^i(S) = 0` for all `S`
implies `φ_i(v) = 0`. -/
theorem satisfiesDummy_of_symmetric_marginal {n : ℕ} (φ : Game n → Fin n → ℝ)
    (hA : IsAllocationProcedure φ) (hS : IsSymmetric φ) (hM : IsMarginal φ) :
    SatisfiesDummy φ := by sorry

end MonotonicSolutions.StrongMono
