import Mathlib
import Definitions.Def_ZhengQR_CostBounds_QRMachinery

namespace ZhengQR.CostBounds

open MeasureTheory

/-- p. 88: the expected inventory-cost rate `G(y) = E[h (y − D)⁺ + p (D − y)⁺]` when the leadtime
demand `D` has distribution `μ`. -/
noncomputable def newsvendorCost (μ : Measure ℝ) (h p y : ℝ) : ℝ :=
  ∫ x, (h * max (y - x) 0 + p * max (x - y) 0) ∂μ

/-- p. 94: the inventory-cost rate of the deterministic (EOQ) model,
`G_d(y) = h (y − λL)⁺ + p (λL − y)⁺`. -/
noncomputable def eoqInvCost (lam L h p y : ℝ) : ℝ :=
  h * max (y - lam * L) 0 + p * max (lam * L - y) 0

/-- Eq. (20), p. 94: the EOQ order quantity `Q*_d = √(2λK(h + p)/(hp))`. -/
noncomputable def eoqQty (lam K h p : ℝ) : ℝ :=
  Real.sqrt (2 * lam * K * (h + p) / (h * p))

/-- The standing assumptions of §1–§2 (pp. 88–90): demand rate `λ`, leadtime `L`, fixed ordering
cost `K`, holding and backorder cost rates `h`, `p`, all positive; the leadtime demand `D` has
distribution `μ`, a probability measure on `ℝ` concentrated on `[0, ∞)`, integrable, with mean
`E(D) = λL`; and `G` attains its minimum at a unique point (p. 90). -/
structure QRModel where
  lam : ℝ
  L : ℝ
  K : ℝ
  h : ℝ
  p : ℝ
  μ : Measure ℝ
  lam_pos : 0 < lam
  L_pos : 0 < L
  K_pos : 0 < K
  h_pos : 0 < h
  p_pos : 0 < p
  isProb : IsProbabilityMeasure μ
  integrable_id : Integrable (fun x : ℝ => x) μ
  mean_eq : ∫ x, x ∂μ = lam * L
  demand_nonneg : ∀ᵐ x ∂μ, 0 ≤ x
  unique_min : ∃! y : ℝ, ∀ z : ℝ, newsvendorCost μ h p y ≤ newsvendorCost μ h p z

namespace QRModel

/-- The stochastic model's inventory-cost rate `G`. -/
noncomputable def G (M : QRModel) : ℝ → ℝ := newsvendorCost M.μ M.h M.p

/-- The EOQ model's inventory-cost rate `G_d` (same parameters, demand constant at `λL`). -/
noncomputable def Gd (M : QRModel) : ℝ → ℝ := eoqInvCost M.lam M.L M.h M.p

/-- The EOQ order quantity `Q*_d` of the model. -/
noncomputable def Qd (M : QRModel) : ℝ := eoqQty M.lam M.K M.h M.p

end QRModel

end ZhengQR.CostBounds
