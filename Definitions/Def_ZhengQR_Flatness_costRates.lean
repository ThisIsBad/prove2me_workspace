import Mathlib

namespace ZhengQR.Flatness

/-- Zheng (1992), p. 88: the expected inventory cost rate `G(y) = E[h(y - D)⁺ + p(D - y)⁺]`
of the stochastic `(Q, r)` model, where the leadtime demand `D` has distribution `μ`,
`h` is the holding cost rate and `p` the backorder penalty rate. -/
noncomputable def newsvendorCost (h p : ℝ) (μ : MeasureTheory.Measure ℝ) (y : ℝ) : ℝ :=
  ∫ x, (h * max (y - x) 0 + p * max (x - y) 0) ∂μ

/-- Zheng (1992), p. 94: the inventory cost rate of the deterministic EOQ model,
`G_d(y) = h(y - λL)⁺ + p(λL - y)⁺`, i.e. `G` for a leadtime demand constant at `λL`. -/
noncomputable def eoqCost (h p lam L : ℝ) (y : ℝ) : ℝ :=
  h * max (y - lam * L) 0 + p * max (lam * L - y) 0

end ZhengQR.Flatness
