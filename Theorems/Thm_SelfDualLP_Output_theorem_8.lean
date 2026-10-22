import Mathlib
import Definitions.Def_SelfDualLP_Complexity_LPData
import Definitions.Def_SelfDualLP_Output_HLP
import Definitions.Def_SelfDualLP_Output_Neighborhood
import Definitions.Def_SelfDualLP_Output_PCSequence

open Matrix

namespace SelfDualLP.Output

/-- Theorem 8 (p. 63), with `β = 1/4`. Let `(yᵏ, xᵏ, τᵏ, θᵏ, sᵏ, κᵏ)` be the iterates of the
predictor–corrector algorithm on (HLP) under (7).
* If (LP) possesses an optimal solution, then `τᵏ ≥ (1 − 2β)/(eᵀx̄ + eᵀs̄ + 1)` for all `k`,
  where `x̄` and `(ȳ, s̄)` are any optimal solution pair for (LP) and (LD);
* otherwise there is a fixed `ε > 0`, independent of `k`, such that for all `k`
  `κᵏ ≥ (1 − 2β)ε/(n + 1)` and
  `(1 − 2β)/(2(n + 1)) ≤ (1 − 2β)/κᵏ ≤ τᵏ/θᵏ ≤ (1 + 2β)/κᵏ ≤ (n + 1)(1 + 2β)/((1 − 2β)ε)`. -/
theorem theorem_8 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (z : ℕ → HLPPoint m n) (hz : IsPCSequence A b c z) :
    (SelfDualLP.Complexity.LPHasSolution A b c →
      ∀ (xbar : Fin n → ℝ) (ybar : Fin m → ℝ) (sbar : Fin n → ℝ),
        SelfDualLP.Complexity.LPOptimal A b c xbar → SelfDualLP.Complexity.LDOptimal A b c ybar sbar →
        ∀ k, (1 - 2 * beta) / (ones n ⬝ᵥ xbar + ones n ⬝ᵥ sbar + 1) ≤ (z k).τ) ∧
    (¬ SelfDualLP.Complexity.LPHasSolution A b c →
      ∃ ε : ℝ, 0 < ε ∧ ∀ k,
        (1 - 2 * beta) * ε / ((n : ℝ) + 1) ≤ (z k).κ ∧
        (1 - 2 * beta) / (2 * ((n : ℝ) + 1)) ≤ (1 - 2 * beta) / (z k).κ ∧
        (1 - 2 * beta) / (z k).κ ≤ (z k).τ / (z k).θ ∧
        (z k).τ / (z k).θ ≤ (1 + 2 * beta) / (z k).κ ∧
        (1 + 2 * beta) / (z k).κ ≤ ((n : ℝ) + 1) * (1 + 2 * beta) / ((1 - 2 * beta) * ε)) := by sorry
end SelfDualLP.Output

