import Mathlib
import Definitions.Def_CachonPushPull_Pareto_Model

namespace CachonPushPull.Pareto

open MeasureTheory ProbabilityTheory

/-! ### Push contracts (§4.2, p. 227) -/

/-- Push retailer's expected profit with prebook `q` at wholesale price `ŵ₁ = w`:
`π̂_r(q, ŵ₁) = (p - v) S(q) - (ŵ₁ - v) q`. -/
noncomputable def pushRetailerProfitAt (μ : Measure ℝ) (p v w q : ℝ) : ℝ :=
  (p - v) * S μ q - (w - v) * q

/-- Push supplier's profit `π̂_s(q, ŵ₁) = (ŵ₁ - c) q`. -/
def pushSupplierProfitAt (c w q : ℝ) : ℝ :=
  (w - c) * q

/-- The push wholesale price that induces prebook `q`, solved from Eq. (3):
`ŵ₁(q) = p - (p - v) F(q)`. -/
noncomputable def pushPrice (μ : Measure ℝ) (p v q : ℝ) : ℝ :=
  p - (p - v) * cdf μ q

/-- `π̂_r(q) = π̂_r(q, ŵ₁(q))`. -/
noncomputable def pushRetailerProfit (μ : Measure ℝ) (p v q : ℝ) : ℝ :=
  pushRetailerProfitAt μ p v (pushPrice μ p v q) q

/-- `π̂_s(q) = π̂_s(q, ŵ₁(q))`. -/
noncomputable def pushSupplierProfit (μ : Measure ℝ) (p c v q : ℝ) : ℝ :=
  pushSupplierProfitAt c (pushPrice μ p v q) q

/-! ### Pull contracts (§4.3, pp. 227–228) -/

/-- Pull supplier's expected profit with production `q` at wholesale price `w₁ = w₂ = w`:
`π_s(q, w₁) = (w₁ - v) S(q) - (c - v) q`. -/
noncomputable def pullSupplierProfitAt (μ : Measure ℝ) (c v w q : ℝ) : ℝ :=
  (w - v) * S μ q - (c - v) * q

/-- Pull retailer's expected profit `π_r(q, w₁) = (p - w₁) S(q)`. -/
noncomputable def pullRetailerProfitAt (μ : Measure ℝ) (p w q : ℝ) : ℝ :=
  (p - w) * S μ q

/-- The pull wholesale price that induces production `q`, solved from Eq. (7) (Eq. (8)):
`w₁(q) = (c - v F(q)) / (1 - F(q))`. -/
noncomputable def pullPrice (μ : Measure ℝ) (c v q : ℝ) : ℝ :=
  (c - v * cdf μ q) / (1 - cdf μ q)

/-- `π_s(q) = π_s(q, w₁(q))`. -/
noncomputable def pullSupplierProfit (μ : Measure ℝ) (c v q : ℝ) : ℝ :=
  pullSupplierProfitAt μ c v (pullPrice μ c v q) q

/-- `π_r(q) = π_r(q, w₁(q))`. -/
noncomputable def pullRetailerProfit (μ : Measure ℝ) (p c v q : ℝ) : ℝ :=
  pullRetailerProfitAt μ p (pullPrice μ c v q) q

/-! ### The prebook game with wholesale prices `(w₁, w₂)` (§4.5, p. 233) -/

/-- Supplier's profit when the retailer prebooks `y` and the supplier produces `Q ≥ y` (Eq. (20)):
`π_s(y, Q) = (w₁ - v) y + (w₂ - v)(S(Q) - S(y)) - (c - v) Q`. -/
noncomputable def apdSupplierProfit (μ : Measure ℝ) (c v w₁ w₂ y Q : ℝ) : ℝ :=
  (w₁ - v) * y + (w₂ - v) * (S μ Q - S μ y) - (c - v) * Q

/-- `Q` is an optimal production quantity for the supplier given prebook `y`: `Q ≥ y` and `Q`
maximizes `apdSupplierProfit` over all production quantities `Q' ≥ y`. -/
def IsSupplierBestReply (μ : Measure ℝ) (c v w₁ w₂ y Q : ℝ) : Prop :=
  y ≤ Q ∧ ∀ Q' : ℝ, y ≤ Q' → apdSupplierProfit μ c v w₁ w₂ y Q' ≤ apdSupplierProfit μ c v w₁ w₂ y Q

/-- Retailer's expected profit when he prebooks `y` and the supplier produces `Q ≥ y`:
`-(w₁ - v) y + (p - v) S(y) + (p - w₂)(S(Q) - S(y))` (p. 233). For `Q = y` this is the push
profit `(p - v) S(y) - (w₁ - v) y`. -/
noncomputable def apdRetailerProfit (μ : Measure ℝ) (p v w₁ w₂ y Q : ℝ) : ℝ :=
  -(w₁ - v) * y + (p - v) * S μ y + (p - w₂) * (S μ Q - S μ y)

/-- The pull contract with production `q` (single wholesale price `w₁ = w₂ = w₁(q)`) survives the
push challenge (pp. 228, 231): for every prebook `y ≥ 0` the supplier has an optimal production
reply, and every positive prebook `y > 0`, followed by an optimal supplier reply, leaves the
retailer with strictly less expected profit than prebooking zero, followed by an optimal supplier
reply. -/
def SurvivesPushChallenge (μ : Measure ℝ) (p c v q : ℝ) : Prop :=
  (∀ y : ℝ, 0 ≤ y → ∃ Q : ℝ, IsSupplierBestReply μ c v (pullPrice μ c v q) (pullPrice μ c v q) y Q) ∧
  ∀ y Q Q₀ : ℝ, 0 < y →
    IsSupplierBestReply μ c v (pullPrice μ c v q) (pullPrice μ c v q) y Q →
    IsSupplierBestReply μ c v (pullPrice μ c v q) (pullPrice μ c v q) 0 Q₀ →
    apdRetailerProfit μ p v (pullPrice μ c v q) (pullPrice μ c v q) y Q <
      apdRetailerProfit μ p v (pullPrice μ c v q) (pullPrice μ c v q) 0 Q₀

end CachonPushPull.Pareto
