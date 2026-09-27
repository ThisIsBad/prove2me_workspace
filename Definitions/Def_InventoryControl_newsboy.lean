import Mathlib

open MeasureTheory ProbabilityTheory

namespace InventoryControl

/-- The realized cost of the newsboy model: having ordered `S` and seen period demand `x`, the
cost is `co` per unit left unsold and `cu` per unit of demand that could not be met.
Axsäter, *Inventory Control*, Eq. (5.87)-(5.88). -/
noncomputable def newsboyLoss (co cu S x : ℝ) : ℝ := co * max (S - x) 0 + cu * max (x - S) 0

/-- The period demand: normally distributed with mean `m` and standard deviation `s`.
Axsäter, *Inventory Control*, Sect. 5.13. -/
noncomputable def newsboyDemand (m s : ℝ) : Measure ℝ := gaussianReal m (Real.toNNReal (s ^ 2))

@[simp] lemma newsboyDemand_eq (m s : ℝ) :
    newsboyDemand m s = gaussianReal m (Real.toNNReal (s ^ 2)) := rfl

instance instIsProbabilityMeasureNewsboyDemand (m s : ℝ) :
    IsProbabilityMeasure (newsboyDemand m s) := by
  rw [newsboyDemand_eq]; infer_instance

/-- The expected cost of ordering `S`. Axsäter, *Inventory Control*, Eq. (5.89). -/
noncomputable def newsboyCost (co cu m s S : ℝ) : ℝ :=
  ∫ x, newsboyLoss co cu S x ∂(newsboyDemand m s)

/-- The demand distribution function, i.e. `Φ((S - m)/s)`, the left-hand side of Eq. (5.91). -/
noncomputable def newsboyCDF (m s S : ℝ) : ℝ := cdf (newsboyDemand m s) S

/-- The standard normal loss function `G(x) = ∫_x^∞ (v - x) φ(v) dv`.
Axsäter, *Inventory Control*, Eq. (5.40) and Appendix 2. -/
noncomputable def normalLoss (x : ℝ) : ℝ :=
  ∫ v in Set.Ioi x, (v - x) * gaussianPDFReal 0 1 v

end InventoryControl
