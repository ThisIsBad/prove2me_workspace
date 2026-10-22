import Definitions.Def_SelfDualLP_Regularity_HLP

open Matrix

namespace SelfDualLP.Regularity

/-- Ye--Todd--Mizuno (1994), Theorem 2(iv), p. 57. -/
theorem theorem_2_iv {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x₀ : Fin n → ℝ) (y₀ : Fin m → ℝ) (s₀ : Fin n → ℝ)
    (hx₀ : ∀ j, 0 < x₀ j) (hs₀ : ∀ j, 0 < s₀ j) :
    (∃ w : HLPPoint m n,
      IsHLPOptimal A b c x₀ y₀ s₀ w ∧ HLPObjective x₀ s₀ w = 0) ∧
    ∀ w : HLPPoint m n, HLPFeasible A b c x₀ y₀ s₀ w →
      HLPObjective x₀ s₀ w = w.x ⬝ᵥ w.s + w.τ * w.κ := by sorry

end SelfDualLP.Regularity

