import Mathlib
import Definitions.Def_WhittleGittins_Retirement_BanditProcess

namespace WhittleGittins.Retirement

open MeasureTheory ProbabilityTheory

/-- Theorem 1 (p. 147): the maximal reward `F(x, s, M)` equals `F̂(x, s, M)` of (13); it is
realized by every (measurable) index rule, which at `(x, s)` engages a project maximizing
`Mᵢ(xᵢ, sᵢ)` if this maximal value exceeds `M` and otherwise retires; and no feasible measurable
Markov allocation policy earns more than `F`. -/
theorem theorem1_index_rule {N : ℕ} {X : Fin N → Type*} [∀ i, MeasurableSpace (X i)]
    (B : BanditProcess N X) (x : ∀ j, X j) (s : Fin N → ℕ) (M : ℝ) :
    F B x s M = Fhat B x s M ∧
      (∀ σ : Policy N X, IsMeasurablePolicy σ → IsIndexRule B σ →
        polValue B σ x s M = F B x s M) ∧
      (∀ σ : Policy N X, IsFeasible σ → IsMeasurablePolicy σ →
        polValue B σ x s M ≤ F B x s M) := by sorry

end WhittleGittins.Retirement

