import Mathlib

namespace DiscreteConvex.ConjugacyDualityD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The `EReal`-valued convex Legendre-Fenchel transform. -/
noncomputable def ConvexConjE (F : (V → ℤ) → EReal) (y : V → ℤ) : EReal :=
  sSup {t : EReal | ∃ x : V → ℤ, t = ((∑ i, (y i : ℝ) * (x i : ℝ) : ℝ) : EReal) - F x}

end DiscreteConvex.ConjugacyDualityD
