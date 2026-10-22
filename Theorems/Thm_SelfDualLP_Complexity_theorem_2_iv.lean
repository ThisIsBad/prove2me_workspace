import Mathlib
import Definitions.Def_SelfDualLP_Complexity_HLP

open Matrix

namespace SelfDualLP.Complexity

/-- Theorem 2 (iv) (p. 57). For any `x⁰ > 0`, `s⁰ > 0` and `y⁰`: the optimal value of (HLP) is
zero (there is an optimal solution and its objective value `((x⁰)ᵀs⁰ + 1)θ` is `0`), and every
feasible point `(y, x, τ, θ, s, κ) ∈ 𝓕_h` satisfies `((x⁰)ᵀs⁰ + 1)θ = xᵀs + τκ`. -/
theorem theorem_2_iv {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x0 : Fin n → ℝ) (y0 : Fin m → ℝ) (s0 : Fin n → ℝ)
    (hx0 : ∀ j, 0 < x0 j) (hs0 : ∀ j, 0 < s0 j) :
    (∃ z : HLPPoint m n, HLPOptimal A b c x0 y0 s0 z ∧ hlpObjective x0 s0 z = 0) ∧
    ∀ z : HLPPoint m n, HLPFeasible A b c x0 y0 s0 z →
      (x0 ⬝ᵥ s0 + 1) * z.θ = z.x ⬝ᵥ z.s + z.τ * z.κ := by sorry

end SelfDualLP.Complexity

