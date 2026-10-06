import Mathlib

namespace DiscreteConvex.EconomicEquilibriumB

open Classical
open scoped Pointwise
variable {K : Type*} [Fintype K] [DecidableEq K]
/-- The effective domain `dom U = {x ∈ Zᴷ : U(x) ≠ −∞}` of a utility-type function. -/
def UDom (U : (K → ℤ) → WithBot ℝ) : Set (K → ℤ) := {x | U x ≠ ⊥}

end DiscreteConvex.EconomicEquilibriumB
