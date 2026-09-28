import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_ThreeOpSplitting_Convergence_Nonexpansive
import Definitions.Def_ThreeOpSplitting_Convergence_ThreeOperatorIteration

namespace ThreeOpSplitting.Convergence

/-- Davis–Yin, Proposition 2.1 (Averageness of T), p. 833, with inequality (2.2). -/
theorem proposition_2_1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (T₁ T₂ C : H → H) (β γ : ℝ)
    (hT₁ : IsFirmlyNonexpansive T₁) (hT₂ : IsFirmlyNonexpansive T₂)
    (hβ : 0 < β) (hC : IsCocoercive β C) (hγ0 : 0 < γ) (hγ : γ < 2 * β) :
    IsAveraged (2 * β / (4 * β - γ)) (threeOp γ T₁ T₂ C) ∧
      ∀ z w : H,
        ‖threeOp γ T₁ T₂ C z - threeOp γ T₁ T₂ C w‖ ^ 2 ≤ ‖z - w‖ ^ 2
          - (1 - 2 * β / (4 * β - γ)) / (2 * β / (4 * β - γ))
            * ‖(z - threeOp γ T₁ T₂ C z) - (w - threeOp γ T₁ T₂ C w)‖ ^ 2 := by sorry

end ThreeOpSplitting.Convergence

