import Mathlib
import Definitions.Def_MyersonBargaining_NashSolution_Bargaining

namespace MyersonBargaining.NashSolution

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  {A : ι → Type} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
  [∀ i, Nonempty (A i)] {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]

/-- Section 5, p. 69: an implementation of a bargaining solution is incentive-efficient. -/
theorem implementation_incentive_efficient
    (G : Problem ι A C) (cstar : C) (π : C → (∀ i, A i) → ℝ)
    (hπ : IsChoiceMechanism π ∧ IsBIC G π)
    (hx : IsBargainingSolution G cstar (V G π)) :
    IsIncentiveEfficient G π := by sorry

end MyersonBargaining.NashSolution

