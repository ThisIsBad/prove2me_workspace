import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Operators

namespace DiscountedDP.Stationary

open MeasureTheory ProbabilityTheory

/-- Blackwell (1965), Theorem 7(b), p. 234: essential finiteness yields
a stationary plan optimal among all randomized history-dependent plans. -/
theorem theorem7b_optimal_stationary
    {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
    [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
    (P : Problem S A) (π : MarkovPlan S A) (hπ : EssFinite P π) :
    ∃ f : {g : S → A // Measurable g},
      IsOptimal P (stationary f).toPlan := by sorry

end DiscountedDP.Stationary

