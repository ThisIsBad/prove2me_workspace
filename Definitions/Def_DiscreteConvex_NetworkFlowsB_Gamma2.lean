import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_Boundary

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The objective `Γ2(ξ) = Σ γ(a)ξ(a) + f(∂ξ)`. -/
def Gamma2 (tail head : A → V) (gamma : A → ℝ) (f : (V → ℝ) → WithTop ℝ) (xi : A → ℝ) :
    WithTop ℝ :=
  ((∑ a : A, gamma a * xi a : ℝ) : WithTop ℝ) + f (Boundary tail head xi)

end DiscreteConvex.NetworkFlowsB
