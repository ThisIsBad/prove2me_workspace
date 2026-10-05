import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Operators

namespace DiscountedDP.Stationary

open MeasureTheory ProbabilityTheory

/-- Blackwell (1965), Theorem 7(a), p. 234. The four claims are kept together:
the optimal return, equality of operators, uniqueness of the bounded Borel
solution, and existence of pointwise ε-optimal stationary plans. -/
theorem theorem7a_essentially_countable
    {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
    [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
    (P : Problem S A) (π : MarkovPlan S A) (hπ : EssCountable P π)
    (ustar : S → ℝ) (hu : IsBM ustar)
    (hfix : ∀ s, U P π ustar s = ustar s) :
    (∀ s, ustar s = optReturn P s) ∧
    (∀ u, IsBM u → ∀ s, U P π u s = ⨆ a : A, Ta P a u s) ∧
    (∀ v, IsBM v → (∀ s, v s = ⨆ a : A, Ta P a v s) → v = ustar) ∧
    (∀ ε : ℝ, 0 < ε → ∃ f : {g : S → A // Measurable g},
      IsEOptimal P ε (stationary f).toPlan) := by sorry

end DiscountedDP.Stationary

