import Mathlib
import Definitions.Def_KallenbergLP_SemiMarkov_Discounted

namespace KallenbergLP.SemiMarkov

variable {S U : Type*} [Fintype S] [Fintype U] [Nonempty S] [DecidableEq S] [DecidableEq U]

/-- Theorem 7.2.1. The DRD value vector satisfies every discounted Bellman
inequality and lies below every other vector that does. -/
theorem value_smallest_superharmonic (M : Discounted S U) :
    Superharmonic M (value M) ∧
      ∀ w : S → ℝ, Superharmonic M w → ∀ i : S, value M i ≤ w i := by sorry

end KallenbergLP.SemiMarkov

