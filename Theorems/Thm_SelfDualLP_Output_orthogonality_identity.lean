import Mathlib
import Definitions.Def_SelfDualLP_Complexity_LPData
import Definitions.Def_SelfDualLP_Output_HLP
import Definitions.Def_SelfDualLP_Output_Neighborhood
import Definitions.Def_SelfDualLP_Output_PCSequence

open Matrix

namespace SelfDualLP.Output

/-- Proof of Theorem 8 (p. 63), orthogonality identity, under (7). Let `z = (y, x, τ, θ, s, κ) ∈ 𝓕_h`
and let `w = (y*, x*, τ*, θ*, s*, κ*)` be a self-complementary (optimal) solution of (HLP) with
`κ* = 0`. Then `(x − x*)ᵀ(s − s*) + (τ − τ*)(κ − κ*) = 0`, which can be rewritten as
`xᵀs* + sᵀx* + κτ* = (n + 1)μ = (n + 1)θ`, where `μ = (xᵀs + τκ)/(n + 1)`. -/
theorem orthogonality_identity {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (z w : HLPPoint m n) (hz : HLPFeasible7 A b c z)
    (hw : HLPOptimal7 A b c w) (hκ : w.κ = 0) :
    (z.x - w.x) ⬝ᵥ (z.s - w.s) + (z.τ - w.τ) * (z.κ - w.κ) = 0 ∧
    z.x ⬝ᵥ w.s + z.s ⬝ᵥ w.x + z.κ * w.τ = ((n : ℝ) + 1) * mu z ∧
    ((n : ℝ) + 1) * mu z = ((n : ℝ) + 1) * z.θ := by sorry
end SelfDualLP.Output

