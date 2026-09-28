import Mathlib
import Definitions.Def_MonotonicSolutions_StrongMono_Game
import Definitions.Def_MonotonicSolutions_StrongMono_Axioms

namespace MonotonicSolutions.StrongMono

/-- Young (1985, p. 71): Shapley's dummy axiom (11) combined with his additivity axiom
implies (7): if `φ` satisfies `v^i(S) = 0` for all `S` ⇒ `φ_i(v) = 0`, and
`φ(v + w) = φ(v) + φ(w)` for all games, then `v^i(S) = w^i(S)` for all `S` implies
`φ_i(v) = φ_i(w)`. -/
theorem isMarginal_of_dummy_of_additive {n : ℕ} (φ : Game n → Fin n → ℝ)
    (hD : SatisfiesDummy φ) (hAdd : IsAdditive φ) : IsMarginal φ := by sorry

end MonotonicSolutions.StrongMono
