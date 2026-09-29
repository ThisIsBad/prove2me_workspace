import Mathlib
import Definitions.Def_Supermodularity_Cooperative_ShapleyValue
import Definitions.Def_MonotonicSolutions_StrongMono_Game
import Definitions.Def_MonotonicSolutions_StrongMono_Axioms

namespace MonotonicSolutions.StrongMono

/-- Theorem 2 of Young (1985, p. 70): the Shapley value is the unique symmetric allocation
procedure that is strongly monotonic. For a map `φ` from games on `N = Fin n` to allocations,
`φ` is an (efficient) allocation procedure, symmetric and strongly monotonic if and only if
`φ(v)` is the Shapley value of `v` for every game `v`. -/
theorem shapley_unique_symmetric_strongly_monotonic {n : ℕ} (φ : Game n → Fin n → ℝ) :
    (IsAllocationProcedure φ ∧ IsSymmetric φ ∧ IsStronglyMonotonic φ) ↔
      ∀ v : Game n, φ v = Supermodularity.Cooperative.ShapleyValue v.1 := by sorry

end MonotonicSolutions.StrongMono

