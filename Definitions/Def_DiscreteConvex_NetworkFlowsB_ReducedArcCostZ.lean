import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_Coboundary

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The reduced arc cost, integer flow, real potential. -/
def ReducedArcCostZ (tail head : A → V) (fa : A → ℤ → WithTop ℝ) (p : V → ℝ) (a : A) (t : ℤ) :
    WithTop ℝ :=
  fa a t + ((Coboundary tail head p a * (t : ℝ) : ℝ) : WithTop ℝ)

end DiscreteConvex.NetworkFlowsB
