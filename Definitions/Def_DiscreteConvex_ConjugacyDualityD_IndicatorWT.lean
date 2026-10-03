import Mathlib

namespace DiscreteConvex.ConjugacyDualityD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The `{0,+∞}`-valued indicator function of a set. -/
noncomputable def IndicatorWT (B : Set (V → ℤ)) (z : V → ℤ) : WithTop ℝ := if z ∈ B then 0 else ⊤

end DiscreteConvex.ConjugacyDualityD
