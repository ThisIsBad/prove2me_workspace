import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_ThreeOpSplitting_Convergence_Nonexpansive
import Definitions.Def_ThreeOpSplitting_Convergence_ThreeOperatorIteration

namespace ThreeOpSplitting.Convergence

/-- Davis–Yin, Remark 2.1 (p. 834), inequality (2.4): for `ε̄ ∈ (0, 1)`,
`γ̄ ∈ (0, 2βε̄)` and `ᾱ = 1/(2 - ε̄) < 1`, the operator `T` built with stepsize `γ̄`
satisfies the strengthened inequality (2.4). -/
theorem remark_2_1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (T₁ T₂ C : H → H) (β εbar γbar : ℝ)
    (hT₁ : IsFirmlyNonexpansive T₁) (hT₂ : IsFirmlyNonexpansive T₂)
    (hβ : 0 < β) (hC : IsCocoercive β C)
    (hε0 : 0 < εbar) (hε1 : εbar < 1) (hγ0 : 0 < γbar) (hγ : γbar < 2 * β * εbar) :
    alpha εbar < 1 ∧
      ∀ z w : H,
        ‖threeOp γbar T₁ T₂ C z - threeOp γbar T₁ T₂ C w‖ ^ 2 ≤ ‖z - w‖ ^ 2
          - (1 - alpha εbar) / alpha εbar
            * ‖(z - threeOp γbar T₁ T₂ C z) - (w - threeOp γbar T₁ T₂ C w)‖ ^ 2
          - γbar * (2 * β - γbar / εbar) * ‖C (T₂ z) - C (T₂ w)‖ ^ 2 := by sorry

end ThreeOpSplitting.Convergence

