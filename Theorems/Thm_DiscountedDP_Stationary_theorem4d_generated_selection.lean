import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Operators

namespace DiscountedDP.Stationary

open MeasureTheory ProbabilityTheory

/-- Blackwell (1965), Theorem 4(d), p. 231. -/
theorem theorem4d_generated_selection
    {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
    [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
    (P : Problem S A) (π : MarkovPlan S A) (u : S → ℝ)
    (hu : IsBM u) (ε : ℝ) (hε : 0 < ε) :
    ∃ f : {g : S → A // Measurable g}, IsGenerated π f ∧
      ∀ s, U P π u s - ε ≤ T P f u s := by sorry

end DiscountedDP.Stationary

