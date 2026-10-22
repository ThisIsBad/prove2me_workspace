import Mathlib
import Definitions.Def_SelfDualLP_Complexity_LPData
import Definitions.Def_SelfDualLP_Output_HLP
import Definitions.Def_SelfDualLP_Output_Neighborhood
import Definitions.Def_SelfDualLP_Output_PCSequence

open Matrix

namespace SelfDualLP.Output

/-- Proof of Theorem 8, first sentence (p. 63): every iterate of the predictor–corrector
algorithm lies in `𝒩(2β)`, `2β = 1/2`. The second conjunct, `θᵏ ≤ 1 = θ⁰`, is the monotonicity
of `θᵏ` given by the step ratios of p. 62 (`θᵏ⁺¹/θᵏ ≤ 1 − 8^{−1/4}/√(n+1)` on predictor steps,
`= 1` on corrector steps); the proof of Theorem 8 uses it in `κᵏ ≤ (n+1) + (n+1)θᵏ ≤ 2(n+1)`. -/
theorem sequence_in_neighborhood {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (z : ℕ → HLPPoint m n) (hz : IsPCSequence A b c z) :
    ∀ k, Nbhd A b c (2 * beta) (z k) ∧ (z k).θ ≤ 1 := by sorry
end SelfDualLP.Output

