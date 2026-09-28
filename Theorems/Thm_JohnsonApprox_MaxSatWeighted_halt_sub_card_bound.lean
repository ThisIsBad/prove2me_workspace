import Mathlib
import Definitions.Def_JohnsonApprox_Shared_Problem
import Definitions.Def_JohnsonApprox_MaxSatWeighted_B2

namespace JohnsonApprox.MaxSatWeighted

/-- Proof of Theorem 3 (p. 264): when B2 halts on an input `S` of `MS(k)`,
`|LEFT| ≤ |S|/2^k` and `|SUB| ≥ |S|(1 − 1/2^k)`, stated without division. -/
theorem halt_sub_card_bound (k : ℕ) (S : Finset Shared.Clause) (hS : Shared.InMS k S) (σ : State)
    (hσ : Reachable S σ) (hhalt : Halts σ) :
    2 ^ k * σ.LEFT.card ≤ S.card ∧ (2 ^ k - 1) * S.card ≤ 2 ^ k * σ.SUB.card := by sorry

end JohnsonApprox.MaxSatWeighted

