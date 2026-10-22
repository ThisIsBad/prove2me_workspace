import Mathlib
import Definitions.Def_SelfDualLP_Complexity_HLP

open Matrix

namespace SelfDualLP.Complexity

/-- Theorem 2 (ii) (p. 57). For any `x⁰ > 0`, `s⁰ > 0` and `y⁰`, (HLP) has the strictly
feasible point `(y, x, τ, θ, s, κ) = (y⁰, x⁰, 1, 1, s⁰, 1)`. -/
theorem theorem_2_ii {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x0 : Fin n → ℝ) (y0 : Fin m → ℝ) (s0 : Fin n → ℝ)
    (hx0 : ∀ j, 0 < x0 j) (hs0 : ∀ j, 0 < s0 j) :
    HLPStrictlyFeasible A b c x0 y0 s0 ⟨y0, x0, 1, 1, s0, 1⟩ := by sorry

end SelfDualLP.Complexity

