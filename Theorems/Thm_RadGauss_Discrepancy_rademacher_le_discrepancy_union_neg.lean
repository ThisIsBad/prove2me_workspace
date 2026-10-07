import Definitions.Def_RadGauss_RiskBound_rademacherComplexity
import Definitions.Def_RadGauss_Discrepancy_maxDiscrepancy
import Definitions.Def_RadGauss_Discrepancy_condSup

open MeasureTheory
open scoped ENNReal Pointwise

namespace RadGauss.Discrepancy

/-- Appendix A, p. 480: `R_n(F) = R_n(F ∪ −F) ≤ D_n(F ∪ −F) + 4 √(2/n)` for `n = 2m`. -/
theorem rademacher_le_discrepancy_union_neg {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (m : ℕ) (hm : 0 < m) (F : Set (X → ℝ)) (hFne : F.Nonempty)
    (hFrange : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1)
    (hFmeas : ∀ f ∈ F, Measurable f)
    (hsup : ∀ σ : Fin (2 * m) → Bool,
      Measurable fun x : Fin (2 * m) → X => ⨆ f : F, ∑ i, RadGauss.RiskBound.signVal (σ i) * (f : X → ℝ) (x i)) :
    RadGauss.RiskBound.rademacherComplexity μ (2 * m) F = RadGauss.RiskBound.rademacherComplexity μ (2 * m) (F ∪ -F) ∧
      RadGauss.RiskBound.rademacherComplexity μ (2 * m) (F ∪ -F)
        ≤ ENNReal.ofReal (expectedMaxDiscrepancy μ m (F ∪ -F))
          + ENNReal.ofReal (4 * Real.sqrt (2 / ((2 * m : ℕ) : ℝ))) := by sorry

end RadGauss.Discrepancy

