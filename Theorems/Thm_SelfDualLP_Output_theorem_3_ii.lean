import Mathlib
import Definitions.Def_SelfDualLP_Complexity_LPData
import Definitions.Def_SelfDualLP_Output_HLP
import Definitions.Def_SelfDualLP_Output_Neighborhood
import Definitions.Def_SelfDualLP_Output_PCSequence

open Matrix

namespace SelfDualLP.Output

/-- Theorem 3 (ii) (p. 58), under the choice (7). Let `(y*, x*, τ*, θ* = 0, s*, κ*)` be a
strictly self-complementary solution of (HLP) with `τ* = 0`. Then `κ* > 0`, hence
`cᵀx* − bᵀy* < 0`, i.e. at least one of `cᵀx*` and `−bᵀy*` is negative; if `cᵀx* < 0` then
(LD) is infeasible; if `−bᵀy* < 0` then (LP) is infeasible; and if both are negative then both
(LP) and (LD) are infeasible. -/
theorem theorem_3_ii {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (z : HLPPoint m n) (hz : StrictlySelfComplementary7 A b c z) (hτ : z.τ = 0) :
    0 < z.κ ∧ c ⬝ᵥ z.x - b ⬝ᵥ z.y < 0 ∧ (c ⬝ᵥ z.x < 0 ∨ -(b ⬝ᵥ z.y) < 0) ∧
    (c ⬝ᵥ z.x < 0 → ¬ SelfDualLP.Complexity.LDIsFeasible A c) ∧
    (-(b ⬝ᵥ z.y) < 0 → ¬ SelfDualLP.Complexity.LPIsFeasible A b c) ∧
    (c ⬝ᵥ z.x < 0 ∧ -(b ⬝ᵥ z.y) < 0 → ¬ SelfDualLP.Complexity.LPIsFeasible A b c ∧ ¬ SelfDualLP.Complexity.LDIsFeasible A c) := by sorry
end SelfDualLP.Output

