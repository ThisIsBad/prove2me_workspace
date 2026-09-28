import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_ThreeOpSplitting_Convergence_ThreeOperatorIteration

namespace ThreeOpSplitting.Convergence

/-- Davis–Yin, Lemma 2.2 (Fixed-point encoding), p. 832:
`zer(A + B + C) = J_{γB}(Fix T)` and
`Fix T = {x + γ u | 0 ∈ (A + B + C) x, u ∈ B x ∩ (-A x - C x)}`. -/
theorem lemma_2_2 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A B : H → Set H) (C : H → H) (β γ : ℝ) (JA JB : H → H)
    (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B)
    (hβ : 0 < β) (hC : IsCocoercive β C) (hγ : 0 < γ)
    (hJA : IsResolvent γ A JA) (hJB : IsResolvent γ B JB) :
    zer (opSum A B C) = JB '' Function.fixedPoints (threeOp γ JA JB C) ∧
      Function.fixedPoints (threeOp γ JA JB C) =
        {z : H | ∃ x u : H, (0 : H) ∈ opSum A B C x ∧ u ∈ B x ∧
          (∃ a ∈ A x, u = -a - C x) ∧ z = x + γ • u} := by sorry

end ThreeOpSplitting.Convergence

