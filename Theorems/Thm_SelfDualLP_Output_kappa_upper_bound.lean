import Mathlib
import Definitions.Def_SelfDualLP_Complexity_LPData
import Definitions.Def_SelfDualLP_Output_HLP
import Definitions.Def_SelfDualLP_Output_Neighborhood
import Definitions.Def_SelfDualLP_Output_PCSequence

open Matrix

namespace SelfDualLP.Output

/-- Proof of Theorem 8 (p. 63): along every predictor–corrector sequence, relation (9) gives
`κᵏ ≤ (n + 1) + (n + 1)θᵏ ≤ 2(n + 1)` for all `k`. -/
theorem kappa_upper_bound {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (z : ℕ → HLPPoint m n) (hz : IsPCSequence A b c z) :
    ∀ k, (z k).κ ≤ ((n : ℝ) + 1) + ((n : ℝ) + 1) * (z k).θ ∧
      ((n : ℝ) + 1) + ((n : ℝ) + 1) * (z k).θ ≤ 2 * ((n : ℝ) + 1) := by sorry
end SelfDualLP.Output

