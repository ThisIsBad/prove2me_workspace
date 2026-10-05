import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Operators

namespace DiscountedDP.Stationary

open MeasureTheory ProbabilityTheory

/-- Blackwell (1965), Theorem 3(c), p. 231: prefixing a Markov plan
by a rule applies that rule's one-step operator to its return. -/
theorem theorem3c_prefix_return
    {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
    [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
    (P : Problem S A) (f : {g : S → A // Measurable g})
    (π : MarkovPlan S A) :
    ∀ s, T P f (I P π.toPlan) s =
      I P (MarkovPlan.cons f π).toPlan s := by sorry

end DiscountedDP.Stationary

