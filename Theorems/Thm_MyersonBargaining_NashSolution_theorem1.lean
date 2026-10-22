import Mathlib
import Definitions.Def_MyersonBargaining_NashSolution_Bargaining

namespace MyersonBargaining.NashSolution

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  {A : ι → Type} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
  [∀ i, Nonempty (A i)] {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]

/-- Theorem 1, p. 64: the incentive-feasible set is nonempty, convex, compact, and feasible. -/
theorem theorem1 (G : Problem ι A C) :
    (FStar G).Nonempty ∧ Convex ℝ (FStar G) ∧ IsCompact (FStar G) ∧
      FStar G ⊆ F G := by sorry

end MyersonBargaining.NashSolution

