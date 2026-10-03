import Mathlib
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_ConvexClosureR

namespace DiscreteConvex.EconomicEquilibriumB

open Classical
open scoped Pointwise
variable {K : Type*} [Fintype K] [DecidableEq K]
/-- The continuous supply set `Ŝl(p) = arg max (⟨p,y⟩ − Ĉl(y))`. -/
def ContSupplySet (C : (K → ℤ) → WithTop ℝ) (p : K → ℝ) : Set (K → ℝ) :=
  {y | ∀ z : K → ℝ,
    ((∑ k, p k * z k : ℝ) : EReal) + (-ConvexClosureR C z) ≤
      ((∑ k, p k * y k : ℝ) : EReal) + (-ConvexClosureR C y)}

end DiscreteConvex.EconomicEquilibriumB
