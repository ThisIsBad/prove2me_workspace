import Mathlib
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_ToERealOfBot

namespace DiscreteConvex.EconomicEquilibriumB

open Classical
open scoped Pointwise
variable {K : Type*} [Fintype K] [DecidableEq K]
/-- The concave closure `Û` of a utility-type function `U`. -/
noncomputable def ConcaveClosureR (U : (K → ℤ) → WithBot ℝ) (x : K → ℝ) : EReal :=
  sInf {v : EReal | ∃ (p : K → ℝ) (alpha : ℝ),
    (∀ y : K → ℤ, ToERealOfBot (U y) ≤ ((alpha + ∑ k, p k * (y k : ℝ) : ℝ) : EReal)) ∧
    v = ((alpha + ∑ k, p k * x k : ℝ) : EReal)}

end DiscreteConvex.EconomicEquilibriumB
