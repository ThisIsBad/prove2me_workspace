import Mathlib
import Definitions.Def_SelfDualLP_Complexity_LPData
import Definitions.Def_SelfDualLP_Output_HLP
import Definitions.Def_SelfDualLP_Output_Neighborhood
import Definitions.Def_SelfDualLP_Output_PCSequence

open Matrix

namespace SelfDualLP.Output

/-- Proof of Theorem 8 (p. 63): if `x̄` is optimal for (LP) and `(ȳ, s̄)` is optimal for (LD), then
with `α = (n + 1)/(eᵀx̄ + eᵀs̄ + 1) > 0` the point
`(y*, x*, τ*, θ*, s*, κ*) = (αȳ, αx̄, α, 0, αs̄, 0)` is a self-complementary (i.e. optimal)
solution of (HLP) under (7). -/
theorem optimal_pair_solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (xbar : Fin n → ℝ) (ybar : Fin m → ℝ) (sbar : Fin n → ℝ)
    (hx : SelfDualLP.Complexity.LPOptimal A b c xbar) (hy : SelfDualLP.Complexity.LDOptimal A b c ybar sbar) :
    0 < ((n : ℝ) + 1) / (ones n ⬝ᵥ xbar + ones n ⬝ᵥ sbar + 1) ∧
    HLPOptimal7 A b c
      (let α : ℝ := ((n : ℝ) + 1) / (ones n ⬝ᵥ xbar + ones n ⬝ᵥ sbar + 1)
       ⟨α • ybar, α • xbar, α, 0, α • sbar, 0⟩) := by sorry
end SelfDualLP.Output

