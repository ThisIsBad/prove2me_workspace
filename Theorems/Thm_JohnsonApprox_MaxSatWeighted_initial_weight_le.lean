import Mathlib
import Definitions.Def_JohnsonApprox_Shared_Problem
import Definitions.Def_JohnsonApprox_MaxSatWeighted_B2

namespace JohnsonApprox.MaxSatWeighted

/-- Proof of Theorem 3 (p. 263): initially, the total weight of the clauses in `LEFT` is at most
`|S|/2^k` when every clause of `S` has at least `k` literals. -/
theorem initial_weight_le (k : ℕ) (S : Finset Shared.Clause) (hS : Shared.InMS k S) :
    (init S).weight (init S).LEFT ≤ (S.card : ℚ) / 2 ^ k := by sorry

end JohnsonApprox.MaxSatWeighted

