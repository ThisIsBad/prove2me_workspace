import Mathlib
import Definitions.Def_NashVecOpt_SharedConstraint_Model

namespace NashVecOpt.SharedConstraint

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {E : ι → Type} [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]

/-- Theorem 2.6, p. 7: the Nash equilibria of a shared-constraint game are exactly the
Pareto minimizers of its augmented objective under cone (6). -/
theorem theorem_2_6 (hN : 2 ≤ Fintype.card ι) (f : ι → (∀ j, E j) → ℝ)
    (X : Set (∀ j, E j)) :
    NE f X = vArgMin (orderCone (E := E)) (obj f) X := by sorry

end NashVecOpt.SharedConstraint

