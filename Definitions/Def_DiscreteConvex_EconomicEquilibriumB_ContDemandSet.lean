import Mathlib
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_ConcaveClosureR

namespace DiscreteConvex.EconomicEquilibriumB

open Classical
open scoped Pointwise
variable {K : Type*} [Fintype K] [DecidableEq K]
/-- The continuous demand set `D̂h(p) = arg max (Ûh(x) − ⟨p,x⟩)`. -/
def ContDemandSet (U : (K → ℤ) → WithBot ℝ) (p : K → ℝ) : Set (K → ℝ) :=
  {x | ∀ z : K → ℝ,
    ConcaveClosureR U z + ((-(∑ k, p k * z k) : ℝ) : EReal) ≤
      ConcaveClosureR U x + ((-(∑ k, p k * x k) : ℝ) : EReal)}

end DiscreteConvex.EconomicEquilibriumB
