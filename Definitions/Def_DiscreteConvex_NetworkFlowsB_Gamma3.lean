import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_Boundary

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The objective `Γ3(ξ) = Σ fa(ξ(a)) + f(∂ξ)`. -/
def Gamma3 (tail head : A → V) (fa : A → ℝ → WithTop ℝ) (f : (V → ℝ) → WithTop ℝ) (xi : A → ℝ) :
    WithTop ℝ :=
  (∑ a : A, fa a (xi a)) + f (Boundary tail head xi)

end DiscreteConvex.NetworkFlowsB
