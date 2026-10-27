import Mathlib
import Definitions.Def_ThresholdMNL_Pricing_Model

namespace ThresholdMNL.Pricing

/-- Proof of Theorem 2, first claim (OS p. 1): if `α̂_j > α̂_k` but `u_k > u_j`, giving `j` the markup
`m_k + (α̂_j − α̂_k)/β` and `k` the markup `m_j − (α̂_j − α̂_k)/β` swaps the two nominal utilities,
keeps the outside option's status, keeps every product considered if all were, keeps the total
attractiveness, and strictly raises the profit (provided `k` is considered). -/
theorem exchange_step {N : ℕ} (α c : Fin N → ℝ) (β u0 Δ : ℝ) (hβ : 0 < β) (hΔ : 0 ≤ Δ)
    (S : Finset (Fin N)) (p : Fin N → ℝ) (j k : Fin N) (hj : j ∈ S) (hk : k ∈ S)
    (hα : α k - β * c k < α j - β * c j)
    (hu : nomUtil α β p j < nomUtil α β p k)
    (hkin : InCons S α β u0 Δ p k) :
    let d := ((α j - β * c j) - (α k - β * c k)) / β
    let p' := Function.update (Function.update p j (c j + (p k - c k) + d)) k
                (c k + (p j - c j) - d)
    nomUtil α β p' j = nomUtil α β p k ∧ nomUtil α β p' k = nomUtil α β p j ∧
    (OutsideInCons S α β u0 Δ p' ↔ OutsideInCons S α β u0 Δ p) ∧
    ((∀ i ∈ S, InCons S α β u0 Δ p i) → ∀ i ∈ S, InCons S α β u0 Δ p' i) ∧
    consDenom S α β u0 Δ p' = consDenom S α β u0 Δ p ∧
    profit S α c β u0 Δ p < profit S α c β u0 Δ p' := by sorry

end ThresholdMNL.Pricing

