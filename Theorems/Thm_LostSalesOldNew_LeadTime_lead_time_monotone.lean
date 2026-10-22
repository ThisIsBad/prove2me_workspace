import Mathlib
import Definitions.Def_LostSalesOldNew_LeadTime_Model

namespace LostSalesOldNew.LeadTime

open MeasureTheory

theorem lead_time_monotone (K : Costs) (D : Measure ℝ) [IsProbabilityMeasure D]
    (hD : LostSalesOldNew.StateReduction.IsDemand D) (hmean : Integrable (fun d : ℝ => d) D)
    (n : ℕ) (hn : 1 ≤ n) (x : Fin (n + 1) → ℝ) (hx : ∀ i, 0 ≤ x i) :
    fStar K D n (Fin.init x) ≤ ENNReal.ofReal (qL K D n x) + fStar K D (n + 1) x ∧
    ENNReal.ofReal K.γ * ∫⁻ d, fStar K D n (LostSalesOldNew.StateReduction.shift x d) ∂D ≤ fStar K D (n + 1) x := by sorry

end LostSalesOldNew.LeadTime

