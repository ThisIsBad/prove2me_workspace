import Mathlib

namespace GallegoOzerADI.PositiveSetup

/-- The set-up indicator `δ(z) = 1` if `z > 0` and `0` otherwise (p. 1347). -/
noncomputable def setupIndicator (z : ℝ) : ℝ := if 0 < z then 1 else 0

/-- The right-hand side of the functional equation (8) for a single period with set-up cost `K`
and cost-to-go `V` (p. 1349): `min_{y ≥ x} {K δ(y - x) + V y}`, written as an infimum over the
order-up-to levels `y ≥ x`. Attainment of the infimum is never part of this definition; it is
asserted by the theorems that use it. -/
noncomputable def orderCost (K : ℝ) (V : ℝ → ℝ) (x : ℝ) : ℝ :=
  ⨅ y : {y : ℝ // x ≤ y}, (K * setupIndicator ((y : ℝ) - x) + V y)

/-- The function `H(x) ≡ K + min_{y ≥ x} V(y) - V(x)` of p. 1350: ordering from `x` is optimal
when `H(x) ≤ 0` and not optimal when `H(x) > 0`. The minimum is written as an infimum over
`y ≥ x`. -/
noncomputable def reorderGap (K : ℝ) (V : ℝ → ℝ) (x : ℝ) : ℝ :=
  K + (⨅ y : {y : ℝ // x ≤ y}, V y) - V x

end GallegoOzerADI.PositiveSetup
