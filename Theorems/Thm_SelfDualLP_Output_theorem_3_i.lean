import Mathlib
import Definitions.Def_SelfDualLP_Complexity_LPData
import Definitions.Def_SelfDualLP_Output_HLP
import Definitions.Def_SelfDualLP_Output_Neighborhood
import Definitions.Def_SelfDualLP_Output_PCSequence

open Matrix

namespace SelfDualLP.Output

/-- Theorem 3 (i) (p. 58), under the choice (7). Let `(y*, x*, τ*, θ* = 0, s*, κ*)` be a
strictly self-complementary solution of (HLP). Then (LP) has a solution (an optimal solution)
if and only if `τ* > 0`; in this case `x*/τ*` is optimal for (LP) and `(y*/τ*, s*/τ*)` is
optimal for (LD). -/
theorem theorem_3_i {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (z : HLPPoint m n) (hz : StrictlySelfComplementary7 A b c z) :
    (SelfDualLP.Complexity.LPHasSolution A b c ↔ 0 < z.τ) ∧
    (0 < z.τ → SelfDualLP.Complexity.LPOptimal A b c (z.τ⁻¹ • z.x) ∧ SelfDualLP.Complexity.LDOptimal A b c (z.τ⁻¹ • z.y) (z.τ⁻¹ • z.s)) := by sorry
end SelfDualLP.Output

