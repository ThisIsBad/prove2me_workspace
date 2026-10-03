import Mathlib

namespace DiscreteConvex.EconomicEquilibriumB

open Classical
open scoped Pointwise
variable {K : Type*} [Fintype K] [DecidableEq K]
/-- The canonical embedding `R∪{−∞} ↪ R∪{±∞}`. -/
noncomputable def ToERealOfBot (v : WithBot ℝ) : EReal := v.elim ⊥ (fun r => (r : EReal))

end DiscreteConvex.EconomicEquilibriumB
