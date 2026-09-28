import Mathlib

namespace NonmonotoneSubmod.Shared

/-- Symmetric set function (Feige–Mirrokni–Vondrák 2011, Theorem 2.1, p. 1137):
`f (X \ S) = f S` for every `S ⊆ X`; here `Sᶜ = Finset.univ \ S`. -/
def SymmetricSetFun {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ) : Prop :=
  ∀ S : Finset X, f Sᶜ = f S

end NonmonotoneSubmod.Shared
