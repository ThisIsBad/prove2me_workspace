import Mathlib
import Definitions.Def_CappedBaseStock_Model
import Definitions.Def_LostSalesOrderUpTo_Asymptotic_Backorder

noncomputable section

open scoped NNReal

namespace AIMInventory.UnknownBound

/-- The paper's one-period newsvendor cost, used only at nonnegative levels. -/
def cost (P : CappedBaseStock.DemandLaw) (h b y : ℝ) : ℝ :=
  LostSalesOrderUpTo.Asymptotic.backorderCost P.law h b (Real.toNNReal y)

/-- The newsvendor quantity of the demand law. -/
def newsvendor (P : CappedBaseStock.DemandLaw) (h b : ℝ) : ℝ :=
  (LostSalesOrderUpTo.Asymptotic.newsvendorLevel P.law h b : ℝ)

/-- The radius of the projection interval at step `t`. -/
def radius (δ : ℝ) (t : ℕ) : ℝ := Real.rpow (t : ℝ) (δ / 2)

/-- Equation (4), modified in Section 3.1. -/
def stepSize (b h : ℝ) (t : ℕ) : ℝ :=
  1 / (max b h * Real.sqrt (t : ℝ))

/-- Equation (5). The event determining this signal is observable from censored
sales in the perishable inventory system. -/
def signal (h b y : ℝ) (d : ℝ≥0) : ℝ :=
  if (d : ℝ) < y then h else -b

/-- Projection onto the closed interval from zero to `a`. -/
def project (a z : ℝ) : ℝ := max (min z a) 0

/-- A zero-based implementation: index zero is the paper's first period.
After observing demand `d t`, the update projects onto `[0,(t+1)^(δ/2)]`. -/
def modAimRun (δ b h y₁ : ℝ) (d : CappedBaseStock.DemandPath) : ℕ → ℝ
  | 0 => y₁
  | t + 1 =>
      let y := modAimRun δ b h y₁ d t
      project (radius δ (t + 1))
        (y - stepSize b h (t + 1) * signal h b y (d t))

/-- The paper's one-based target and implemented level in the perishable case.
The target in period `t` uses only demands from periods strictly before `t`. -/
def modAimTarget (δ b h y₁ : ℝ) (d : CappedBaseStock.DemandPath) (t : ℕ) : ℝ :=
  modAimRun δ b h y₁ d (t - 1)

/-- Rounds below the threshold in the proof of Theorem 7, Equation (10). -/
def earlyRounds (δ y : ℝ) (T : ℕ) : Finset ℕ :=
  (Finset.Icc 1 T).filter (fun t => (t : ℝ) < Real.rpow y (2 / δ))

/-- Rounds at or above the threshold in the proof of Theorem 7, Equation (11). -/
def lateRounds (δ y : ℝ) (T : ℕ) : Finset ℕ :=
  (Finset.Icc 1 T).filter (fun t => Real.rpow y (2 / δ) ≤ (t : ℝ))

end AIMInventory.UnknownBound
