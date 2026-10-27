import Mathlib
import Definitions.Def_NashVecOpt_SharedConstraint_Model

namespace NashVecOpt.SharedConstraint

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {E : ι → Type} [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]

/-- Lemma 2.7, p. 7: the full-cone minimizers equal the intersection of the player-cone
minimizers. -/
theorem lemma_2_7 (hN : 2 ≤ Fintype.card ι) (f : ι → (∀ j, E j) → ℝ)
    (X : Set (∀ j, E j)) :
    vArgMin (orderCone (E := E)) (obj f) X =
      ⋂ i, vArgMin (coneI (E := E) i) (obj f) X := by sorry

end NashVecOpt.SharedConstraint

