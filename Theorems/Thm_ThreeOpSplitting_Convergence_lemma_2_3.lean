import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_Nonexpansive

open InnerProductSpace

namespace ThreeOpSplitting.Convergence

/-- Davis–Yin, Lemma 2.3 (p. 833), inequality (2.1): for `S := U + T₁ ∘ V` with `U, T₁`
firmly nonexpansive, `V` arbitrary and `W := I - (2U + V)`. -/
theorem lemma_2_3 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (U T₁ V : H → H) (hU : IsFirmlyNonexpansive U) (hT₁ : IsFirmlyNonexpansive T₁) :
    let S : H → H := fun x => U x + T₁ (V x)
    let W : H → H := fun x => x - ((2 : ℝ) • U x + V x)
    ∀ z w : H,
      ‖S z - S w‖ ^ 2 ≤ ‖z - w‖ ^ 2 - ‖(z - S z) - (w - S w)‖ ^ 2
        - 2 * ⟪T₁ (V z) - T₁ (V w), W z - W w⟫_ℝ := by sorry

end ThreeOpSplitting.Convergence

