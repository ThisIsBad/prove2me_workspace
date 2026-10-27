import Mathlib

namespace NashVecOpt.SharedConstraint

/-- The cone-induced relation from §2.1, p. 4. -/
def coneLE {Z : Type} [AddCommGroup Z] (K : Set Z) (a b : Z) : Prop :=
  b - a ∈ K

/-- Definition 2.3, p. 5, for an arbitrary vector objective and feasible set. -/
def vArgMin {D Z : Type} [AddCommGroup Z] (K : Set Z) (g : D → Z)
    (X : Set D) : Set D :=
  {xs | xs ∈ X ∧ ∀ x ∈ X, coneLE K (g x) (g xs) → coneLE K (g xs) (g x)}

end NashVecOpt.SharedConstraint
