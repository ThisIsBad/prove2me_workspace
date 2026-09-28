import Mathlib
import Definitions.Def_JohnsonApprox_Shared_Problem
import Definitions.Def_JohnsonApprox_MaxSatWeighted_B2

namespace JohnsonApprox.MaxSatWeighted

/-- Proof of Theorem 3 (p. 264): when B2 halts, every (dead) clause remaining in `LEFT` has
weight exactly `1`. -/
theorem halt_dead_weight_one (S : Finset Shared.Clause) (σ : State) (hσ : Reachable S σ)
    (hhalt : Halts σ) : ∀ C ∈ σ.LEFT, σ.w C = 1 := by sorry

end JohnsonApprox.MaxSatWeighted

