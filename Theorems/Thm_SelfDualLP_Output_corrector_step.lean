import Mathlib
import Definitions.Def_SelfDualLP_Complexity_LPData
import Definitions.Def_SelfDualLP_Output_HLP
import Definitions.Def_SelfDualLP_Output_Neighborhood
import Definitions.Def_SelfDualLP_Output_PCSequence

open Matrix

namespace SelfDualLP.Output

/-- Proof of Theorem 6, corrector-step claim (p. 62), under (7). Let `zᵏ ∈ 𝒩(1/2)` and let `d`
solve (11)–(12) at `zᵏ` with `γ = 1`. Then `zᵏ⁺¹ = zᵏ + d ∈ 𝒩(1/4)` and
`θᵏ⁺¹/θᵏ = ((xᵏ⁺¹)ᵀsᵏ⁺¹ + τᵏ⁺¹κᵏ⁺¹)/((xᵏ)ᵀsᵏ + τᵏκᵏ) = 1`. -/
theorem corrector_step {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (z d : HLPPoint m n)
    (hz : Nbhd A b c (1 / 2) z) (hd : IsPCDirection A b c z d 1) :
    Nbhd A b c (1 / 4) (z.move d 1) ∧
    (z.move d 1).θ / z.θ = gap (z.move d 1) / gap z ∧
    gap (z.move d 1) / gap z = 1 := by sorry
end SelfDualLP.Output

