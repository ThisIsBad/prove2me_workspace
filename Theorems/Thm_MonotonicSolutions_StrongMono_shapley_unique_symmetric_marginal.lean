import Mathlib
import Definitions.Def_Supermodularity_Cooperative_ShapleyValue
import Definitions.Def_MonotonicSolutions_StrongMono_Game
import Definitions.Def_MonotonicSolutions_StrongMono_Axioms

namespace MonotonicSolutions.StrongMono

/-- Young (1985, p. 71): the proof of Theorem 2 only uses (7). For a map `φ` from games on
`N = Fin n` to allocations, `φ` is an (efficient) allocation procedure, symmetric and
satisfies (7) if and only if `φ(v)` is the Shapley value of `v` for every game `v`. -/
theorem shapley_unique_symmetric_marginal {n : ℕ} (φ : Game n → Fin n → ℝ) :
    (IsAllocationProcedure φ ∧ IsSymmetric φ ∧ IsMarginal φ) ↔
      ∀ v : Game n, φ v = Supermodularity.Cooperative.ShapleyValue v.1 := by sorry

end MonotonicSolutions.StrongMono

