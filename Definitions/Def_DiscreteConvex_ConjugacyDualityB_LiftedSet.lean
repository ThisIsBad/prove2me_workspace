import Mathlib

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The lift of a set `D ⊆ Zⱽ` to `Z^Ṽ`. -/
def LiftedSet (D : Set (V → ℤ)) : Set (Option V → ℤ) :=
  {x | x none = -(∑ v : V, x (some v)) ∧ (fun v => x (some v)) ∈ D}

end DiscreteConvex.ConjugacyDualityB
