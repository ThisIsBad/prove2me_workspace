import Mathlib
import Definitions.Def_Supermodularity_Cooperative_ShapleyValue
import Definitions.Def_MonotonicSolutions_StrongMono_Game
import Definitions.Def_MonotonicSolutions_StrongMono_Axioms

namespace MonotonicSolutions.StrongMono

/-- Young (1985, p. 70, proof of Theorem 2): "It is clear that the Shapley value is strongly
monotonic." For all games `v, w` and every player `i`, if `w^i(S) ≤ v^i(S)` for every
coalition `S`, then `Sh_i(w) ≤ Sh_i(v)`. -/
theorem shapley_isStronglyMonotonic {n : ℕ} :
    IsStronglyMonotonic (fun v : Game n => Supermodularity.Cooperative.ShapleyValue v.1) := by sorry

end MonotonicSolutions.StrongMono
