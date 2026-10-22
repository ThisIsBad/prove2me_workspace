import Definitions.Def_CappedBaseStock_Model

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators

namespace LostSalesOrderUpTo.Asymptotic

/-- The law of demand over the order period and the following lead time. -/
def leadTimeLaw (P : CappedBaseStock.DemandLaw) (τ : ℕ) : Measure ℝ≥0 :=
  Measure.map (fun d : CappedBaseStock.DemandPath =>
    ∑ i ∈ Finset.range (τ + 1), d i) (CappedBaseStock.demandPathLaw P)

/-- Distribution function of the lead-time demand. -/
def distribution (μ : Measure ℝ≥0) (y : ℝ≥0) : ℝ≥0∞ := μ (Set.Iic y)

/-- Expected positive inventory and shortfall, respectively. -/
def expectedHolding (μ : Measure ℝ≥0) (S : ℝ≥0) : ℝ :=
  ∫ d : ℝ≥0, max ((S : ℝ) - (d : ℝ)) 0 ∂μ

def expectedShortfall (μ : Measure ℝ≥0) (S : ℝ≥0) : ℝ :=
  ∫ d : ℝ≥0, max ((d : ℝ) - (S : ℝ)) 0 ∂μ

/-- Stationary order-up-to cost in the backorder system. -/
def backorderCost (μ : Measure ℝ≥0) (h b : ℝ) (S : ℝ≥0) : ℝ :=
  h * expectedHolding μ S + b * expectedShortfall μ S

/-- Best order-up-to cost in the backorder system. -/
def backorderOptimalCost (μ : Measure ℝ≥0) (h b : ℝ) : ℝ :=
  sInf (Set.range (backorderCost μ h b))

/-- Smallest critical-fractile level for the lead-time demand. -/
def newsvendorLevel (μ : Measure ℝ≥0) (h b : ℝ) : ℝ≥0 :=
  sInf {S : ℝ≥0 | ENNReal.ofReal (b / (b + h)) ≤ distribution μ S}

/-- Ratio of expected shortage charge to expected holding charge. -/
def shortageHoldingRatio (μ : Measure ℝ≥0) (h b : ℝ) (S : ℝ≥0) : ℝ :=
  b * expectedShortfall μ S / (h * expectedHolding μ S)

/-- Conditional expected excess over a threshold, with zero at and beyond the upper endpoint. -/
def meanResidualLife (μ : Measure ℝ≥0) (t : ℝ) : ℝ :=
  if 0 < (μ {d : ℝ≥0 | t < (d : ℝ)}).toReal then
    (∫ d : ℝ≥0, max ((d : ℝ) - t) 0 ∂μ) /
      (μ {d : ℝ≥0 | t < (d : ℝ)}).toReal
  else 0

/-- Assumption 1 on the lead-time demand law. -/
def AssumptionOne (μ : Measure ℝ≥0) : Prop :=
  Tendsto (fun t : ℝ => meanResidualLife μ t / t) atTop (nhds 0)

end LostSalesOrderUpTo.Asymptotic
