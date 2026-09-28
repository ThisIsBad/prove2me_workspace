import Mathlib
import Definitions.Def_JohnsonApprox_Shared_Problem
import Definitions.Def_JohnsonApprox_MaxSatWeighted_B2

namespace JohnsonApprox.MaxSatWeighted

/-- Proof of Theorem 3 (pp. 263–264): along any run of B2 on an input of `MS(k)`, one iteration
never increases the total weight of `LEFT`, and so the weight of `LEFT` in every reachable
state (in particular at halting) is at most `|S|/2^k`. -/
theorem left_weight_nonincreasing (k : ℕ) (S : Finset Shared.Clause) (hS : Shared.InMS k S) :
    (∀ σ σ' : State, Reachable S σ → Step σ σ' → σ'.weight σ'.LEFT ≤ σ.weight σ.LEFT) ∧
    (∀ σ : State, Reachable S σ → σ.weight σ.LEFT ≤ (S.card : ℚ) / 2 ^ k) := by sorry

end JohnsonApprox.MaxSatWeighted

