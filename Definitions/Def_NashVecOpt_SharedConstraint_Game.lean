import Mathlib

namespace NashVecOpt.SharedConstraint

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {E : ι → Type} [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]

/-- Definition 2.2, p. 4: feasible unilateral cost minimization in a shared-constraint game. -/
def NE (f : ι → (∀ j, E j) → ℝ) (X : Set (∀ j, E j)) : Set (∀ j, E j) :=
  {xs | xs ∈ X ∧ ∀ (i : ι) (xi : E i), Function.update xs i xi ∈ X →
      f i xs ≤ f i (Function.update xs i xi)}

end NashVecOpt.SharedConstraint
