import Mathlib
import Definitions.Def_CachonCoord_DemandUpdate_Model

open MeasureTheory ProbabilityTheory

namespace CachonCoord.DemandUpdate

namespace Model

variable (M : Model)

/-- p. 65: the retailer's period-2 expected revenue minus period-2 procurement cost under the
buy back contract `{w_1, w_2, b}`, when the supplier delivers in full,
`π_2(q_2|q_1, ξ) = (p − b)S(q_2|ξ) − (w_2 − b)q_2 + w_2 q_1`. -/
noncomputable def retailerProfit2 (w2 b q1 ξ q2 : ℝ) : ℝ :=
  (M.p - b) * M.S ξ q2 - (w2 - b) * q2 + w2 * q1

/-- The retailer's period-1 expected profit `π_1(q_1) = −w_1 q_1 + E[π_2(q_2(q_1, ξ)|q_1, ξ)]`:
he pays `w_1` per unit ordered in period 1 and orders the supply chain optimal `q_2(q_1, ξ)`
(selection `q2sel`) in period 2 (p. 66). -/
noncomputable def retailerProfit1 (w1 w2 b : ℝ) (q2sel : ℝ → ℝ → ℝ) (q1 : ℝ) : ℝ :=
  -w1 * q1 + M.E (fun ξ => M.retailerProfit2 w2 b q1 ξ (q2sel q1 ξ))

/-- p. 65: the supplier's period-2 profit when the supply chain holds `x ≥ q_1` units at the
start of period 2 and the retailer holds `y` units after the supplier's delivery,
`Π_2(y|x, q_1, q_2, ξ) = bS(y|ξ) − by + w_2(y − q_1) − (y − x)c_2` (for `x ≤ y ≤ q_2`). -/
noncomputable def supplierProfit2Fill (w2 b x q1 ξ y : ℝ) : ℝ :=
  b * M.S ξ y - b * y + w2 * (y - q1) - (y - x) * M.c2

/-- p. 66: the supplier's period-2 profit when she fills the retailer's order `q_2` entirely,
`bS(q_2|ξ) − bq_2 + w_2(q_2 − q_1) − (q_2 − x)⁺c_2`, i.e. the p. 65 profit at `y = q_2` with
production `(q_2 − x)⁺`. (The printed first line on p. 66 omits the term `w_2(q_2 − q_1)`,
which does not depend on `x`.) -/
noncomputable def supplierProfit2 (w2 b x q1 q2 ξ : ℝ) : ℝ :=
  b * M.S ξ q2 - b * q2 + w2 * (q2 - q1) - max (q2 - x) 0 * M.c2

/-- p. 66: the supplier's period-1 expected profit as a function of her period-1 production `x`,
`Π_1(x|q_1) = −c_1 x + E[Π_2(x, q_1, q_2, ξ)]` with `q_2 = q_2(q_1, ξ)` (selection `q2sel`). -/
noncomputable def supplierProfit1 (w2 b : ℝ) (q2sel : ℝ → ℝ → ℝ) (q1 x : ℝ) : ℝ :=
  -M.c1 * x + M.E (fun ξ => M.supplierProfit2 w2 b x q1 (q2sel q1 ξ) ξ)

end Model

end CachonCoord.DemandUpdate
