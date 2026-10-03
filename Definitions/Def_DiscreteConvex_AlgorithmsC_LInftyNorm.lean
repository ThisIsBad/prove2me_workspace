import Mathlib

namespace DiscreteConvex.AlgorithmsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The `ℓ∞`-norm of an integer vector. -/
noncomputable def LInftyNorm {W : Type*} [Fintype W] [Nonempty W] (x : W → ℤ) : ℤ :=
  (Finset.univ : Finset W).sup' Finset.univ_nonempty (fun v => |x v|)

end DiscreteConvex.AlgorithmsC
