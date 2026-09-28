import Mathlib
import Definitions.Def_MonotonicSolutions_StrongMono_Game
import Definitions.Def_MonotonicSolutions_StrongMono_Axioms

namespace MonotonicSolutions.StrongMono

/-- Eq. (7) of Young (1985, p. 70): a strongly monotonic map `φ` depends, for each player,
only on that player's marginal contributions: `v^i(S) = w^i(S)` for all `S` implies
`φ_i(v) = φ_i(w)`. -/
theorem isMarginal_of_isStronglyMonotonic {n : ℕ} (φ : Game n → Fin n → ℝ)
    (hφ : IsStronglyMonotonic φ) : IsMarginal φ := by sorry

end MonotonicSolutions.StrongMono
