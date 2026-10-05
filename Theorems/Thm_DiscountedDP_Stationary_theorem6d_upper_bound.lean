import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Operators

namespace DiscountedDP.Stationary

open MeasureTheory ProbabilityTheory

/-- Blackwell (1965), Theorem 6(d), p. 232. -/
theorem theorem6d_upper_bound
    {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
    [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
    (P : Problem S A) (u : S → ℝ) (hu : IsBM u)
    (hupper : ∀ a s, Ta P a u s ≤ u s) :
    ∀ π : Plan (S := S) (A := A), ∀ s, I P π s ≤ u s := by sorry

end DiscountedDP.Stationary

