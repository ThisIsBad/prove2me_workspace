import Mathlib
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_ToEReal

namespace DiscreteConvex.EconomicEquilibriumB

open Classical
open scoped Pointwise
variable {K : Type*} [Fintype K] [DecidableEq K]
/-- The convex closure `Ĉ` of a cost-type function `C`. -/
noncomputable def ConvexClosureR (C : (K → ℤ) → WithTop ℝ) (x : K → ℝ) : EReal :=
  sSup {v : EReal | ∃ (p : K → ℝ) (alpha : ℝ),
    (∀ y : K → ℤ, ((alpha + ∑ k, p k * (y k : ℝ) : ℝ) : EReal) ≤ ToEReal (C y)) ∧
    v = ((alpha + ∑ k, p k * x k : ℝ) : EReal)}

end DiscreteConvex.EconomicEquilibriumB
