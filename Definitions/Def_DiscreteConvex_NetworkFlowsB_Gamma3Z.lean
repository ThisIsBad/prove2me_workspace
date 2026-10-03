import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_BoundaryZ

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The objective `Γ3(ξ) = Σ fa(ξ(a)) + f(∂ξ)`, integer flows. -/
def Gamma3Z (tail head : A → V) (fa : A → ℤ → WithTop ℝ) (f : (V → ℤ) → WithTop ℝ) (xi : A → ℤ) :
    WithTop ℝ :=
  (∑ a : A, fa a (xi a)) + f (BoundaryZ tail head xi)

end DiscreteConvex.NetworkFlowsB
