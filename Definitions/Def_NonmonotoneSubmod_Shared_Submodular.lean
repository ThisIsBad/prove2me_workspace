import Mathlib

namespace NonmonotoneSubmod.Shared

/-- Definition 1.1 (Feige–Mirrokni–Vondrák 2011, p. 1133): a set function `f : 2^X → ℝ` on a
finite ground set `X` is submodular if `f (S ∪ T) + f (S ∩ T) ≤ f S + f T` for all `S, T ⊆ X`. -/
def Submodular {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ) : Prop :=
  ∀ S T : Finset X, f (S ∪ T) + f (S ∩ T) ≤ f S + f T

end NonmonotoneSubmod.Shared
