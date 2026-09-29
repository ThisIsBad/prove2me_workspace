import Mathlib

open MeasureTheory

namespace ZhengQR.EOQHeuristic

/-- The expected inventory-cost rate `G(y) = E[h (y − D)⁺ + p (D − y)⁺]` (p. 88), where the
leadtime demand `D` has distribution `μ`, `h` is the holding and `p` the backorder cost rate. -/
noncomputable def newsvendorCost (μ : Measure ℝ) (h p y : ℝ) : ℝ :=
  ∫ x, (h * max (y - x) 0 + p * max (x - y) 0) ∂μ

/-- The inventory-cost rate of the deterministic (EOQ) model, p. 94:
`G_d(y) = h (y − λL)⁺ + p (λL − y)⁺`. -/
noncomputable def eoqCost (lam L h p y : ℝ) : ℝ :=
  h * max (y - lam * L) 0 + p * max (lam * L - y) 0

/-- The EOQ order quantity with backorders, Eq. (20), p. 94: `Q*_d = √(2λK(h + p)/(hp))`. -/
noncomputable def eoqQty (lam K h p : ℝ) : ℝ :=
  Real.sqrt (2 * lam * K * (h + p) / (h * p))

/-- The standing assumptions of the stochastic `(Q, r)` model (pp. 88, 90, 94): positive demand
rate `lam`, leadtime `L`, holding cost `h` and backorder cost `p`; a leadtime demand distribution
`μ` that is a probability measure on `[0, ∞)` with finite mean `E(D) = λL`; and a newsvendor cost
`G` that attains its minimum at a unique point `y⁰`. -/
structure IsQRModel (lam L h p : ℝ) (μ : Measure ℝ) : Prop where
  lam_pos : 0 < lam
  L_pos : 0 < L
  h_pos : 0 < h
  p_pos : 0 < p
  isProb : IsProbabilityMeasure μ
  integrable : Integrable (fun x : ℝ => x) μ
  mean : ∫ x, x ∂μ = lam * L
  nonneg : ∀ᵐ x ∂μ, 0 ≤ x
  unique_min : ∃! y : ℝ, ∀ z : ℝ, newsvendorCost μ h p y ≤ newsvendorCost μ h p z

end ZhengQR.EOQHeuristic
