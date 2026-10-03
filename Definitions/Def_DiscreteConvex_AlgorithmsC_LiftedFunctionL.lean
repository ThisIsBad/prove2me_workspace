import Mathlib

namespace DiscreteConvex.AlgorithmsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The lift `g̃(p0,p) = g(p - p0·1)` of `g` to `Option V` (Eq. (7.2)/(10.35)). -/
def LiftedFunctionL {W : Type*} [Fintype W] [DecidableEq W] (g : (W → ℤ) → WithTop ℝ) :
    (Option W → ℤ) → WithTop ℝ :=
  fun x => g (fun v => x (some v) - x none)

end DiscreteConvex.AlgorithmsC
