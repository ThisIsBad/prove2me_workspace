import Mathlib

namespace ZhengQR.OrderQty

open MeasureTheory

/-- The standing assumptions of Zheng (1992), pp. 88 and 94, on the distribution `μ` of the
leadtime demand `D`: `μ` is a probability measure on `ℝ`, `D` is integrable, its mean is
`E(D) = λL`, and demand is nonnegative. -/
structure IsLeadtimeDemand (lam L : ℝ) (μ : Measure ℝ) : Prop where
  isProb : IsProbabilityMeasure μ
  integrable : Integrable (fun x : ℝ => x) μ
  mean_eq : ∫ x, x ∂μ = lam * L
  nonneg : ∀ᵐ x ∂μ, 0 ≤ x

/-- The expected inventory cost rate of the stochastic model (p. 88):
`G(y) = E[h (y - D)⁺ + p (D - y)⁺]`, where `D ∼ μ` is the leadtime demand, `h` the holding cost
rate and `p` the backorder penalty rate. -/
noncomputable def newsvendorCost (h p : ℝ) (μ : Measure ℝ) (y : ℝ) : ℝ :=
  ∫ x, (h * max (y - x) 0 + p * max (x - y) 0) ∂μ

/-- The inventory cost rate of the deterministic EOQ model (p. 94):
`G_d(y) = h (y - λL)⁺ + p (λL - y)⁺`, i.e. `G` for a leadtime demand equal to `λL`. -/
noncomputable def eoqCost (lam L h p : ℝ) (y : ℝ) : ℝ :=
  h * max (y - lam * L) 0 + p * max (lam * L - y) 0

/-- Eq. (20), p. 94: the EOQ order quantity with backorders, `Q*_d = √(2λK(h + p)/(hp))`. -/
noncomputable def eoqQty (lam K h p : ℝ) : ℝ :=
  Real.sqrt (2 * lam * K * (h + p) / (h * p))

end ZhengQR.OrderQty
