import Mathlib
import Definitions.Def_LostSalesOldNew_LeadTime_Model

namespace LostSalesOldNew.LeadTime

open MeasureTheory

theorem optimality_equation (K : Costs) (D : Measure ℝ) [IsProbabilityMeasure D]
    (hD : LostSalesOldNew.StateReduction.IsDemand D) (hmean : Integrable (fun d : ℝ => d) D)
    (L : ℕ) (hL : 1 ≤ L) :
    (∀ x : Fin L → ℝ, (∀ i, 0 ≤ x i) → fStar K D L x = bellman K D L (fStar K D L) x) ∧
    ((0 < K.c ∨ 0 < K.hhat) → ∀ x : Fin L → ℝ, (∀ i, 0 ≤ x i) → ∃ z : ℝ, 0 ≤ z ∧
      fStar K D L x = ENNReal.ofReal (qL K D L (Fin.snoc (α := fun _ => ℝ) x z))
        + ENNReal.ofReal K.γ * ∫⁻ d, fStar K D L (LostSalesOldNew.StateReduction.next x z d) ∂D) ∧
    (∀ g : (Fin L → ℝ) → ENNReal,
      (∀ x : Fin L → ℝ, (∀ i, 0 ≤ x i) → g x = bellman K D L g x) →
      ∀ x : Fin L → ℝ, (∀ i, 0 ≤ x i) → fStar K D L x ≤ g x) := by sorry

end LostSalesOldNew.LeadTime

