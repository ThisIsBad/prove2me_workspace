import Mathlib
import Definitions.Def_AIMInventory_UnknownRho_Model

open MeasureTheory
open scoped ENNReal NNReal

namespace AIMInventory.UnknownRho

/-- Lemma 9, p. 13, corrected by the `+1` needed to count the integer
times below `2z/(E[D]-θ)`. The printed bound fails for deterministic demand
and a sufficiently small positive `z`. -/
theorem lemma_9_corrected (P : DemandLaw) (θ z : ℝ)
    (hθ : θ < CappedBaseStock.mean P) (hz : 0 < z)
    (hfourth : Integrable (fun d : ℝ≥0 => (d : ℝ) ^ 4) P.law) :
    expectedK P θ z ≤ ENNReal.ofReal
      (1 + 2 * z / (CappedBaseStock.mean P - θ) +
        8 * Real.pi ^ 2 * centralFourth P /
          (CappedBaseStock.mean P - θ) ^ 4) := by sorry

end AIMInventory.UnknownRho

