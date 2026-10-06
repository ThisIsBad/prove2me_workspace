import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_Coboundary

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The reduced arc cost `fa[δp(a)](t) = fa(t) + δp(a)·t`. -/
def ReducedArcCost (tail head : A → V) (fa : A → ℝ → WithTop ℝ) (p : V → ℝ) (a : A) (t : ℝ) :
    WithTop ℝ :=
  fa a t + ((Coboundary tail head p a * t : ℝ) : WithTop ℝ)

end DiscreteConvex.NetworkFlowsB
