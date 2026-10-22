import Mathlib
import Definitions.Def_SelfDualLP_Complexity_HLP
import Definitions.Def_SelfDualLP_Complexity_Neighborhood
import Definitions.Def_SelfDualLP_Complexity_PCSequence

open Matrix

namespace SelfDualLP.Complexity

/-- Proof of Theorem 6, predictor-step claim (p. 62), under (7). Let `zᵏ ∈ 𝒩(1/4)`, let `d`
solve (11)–(12) at `zᵏ` with `γ = 0`, and let `ᾱ = max {α : zᵏ + αd ∈ 𝒩(1/2)}` (13) (assumed
attained). Then `zᵏ⁺¹ = zᵏ + ᾱd ∈ 𝒩(1/2)` and
`θᵏ⁺¹/θᵏ = ((xᵏ⁺¹)ᵀsᵏ⁺¹ + τᵏ⁺¹κᵏ⁺¹)/((xᵏ)ᵀsᵏ + τᵏκᵏ) ≤ 1 − 8^{−1/4}/√(n + 1)`. -/
theorem predictor_step {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (z d : HLPPoint m n) (αbar : ℝ)
    (hz : Nbhd A b c (1 / 4) z) (hd : IsPCDirection A b c z d 0)
    (hα : IsGreatest {a : ℝ | Nbhd A b c (1 / 2) (z.move d a)} αbar) :
    Nbhd A b c (1 / 2) (z.move d αbar) ∧
    (z.move d αbar).θ / z.θ = gap (z.move d αbar) / gap z ∧
    gap (z.move d αbar) / gap z ≤ 1 - (8 : ℝ) ^ (-(1 / 4 : ℝ)) / Real.sqrt ((n : ℝ) + 1) := by sorry

end SelfDualLP.Complexity

