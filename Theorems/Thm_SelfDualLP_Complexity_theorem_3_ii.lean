import Mathlib
import Definitions.Def_SelfDualLP_Complexity_LPData
import Definitions.Def_SelfDualLP_Complexity_HLP

open Matrix

namespace SelfDualLP.Complexity

/-- Theorem 3 (ii) (p. 58), under the choice (7). Let `(y*, x*, τ*, θ* = 0, s*, κ*)` be a
strictly self-complementary solution of (HLP) with `τ* = 0`. Then `κ* > 0`, hence
`cᵀx* − bᵀy* < 0`, i.e. at least one of `cᵀx*` and `−bᵀy*` is negative; if `cᵀx* < 0` then
(LD) is infeasible, if `−bᵀy* < 0` then (LP) is infeasible (so if both, both are). -/
theorem theorem_3_ii {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (z : HLPPoint m n) (hz : StrictlySelfComplementary7 A b c z) (hτ : z.τ = 0) :
    0 < z.κ ∧ c ⬝ᵥ z.x - b ⬝ᵥ z.y < 0 ∧ (c ⬝ᵥ z.x < 0 ∨ -(b ⬝ᵥ z.y) < 0) ∧
    (c ⬝ᵥ z.x < 0 → ¬ LDIsFeasible A c) ∧
    (-(b ⬝ᵥ z.y) < 0 → ¬ LPIsFeasible A b c) := by sorry

end SelfDualLP.Complexity

