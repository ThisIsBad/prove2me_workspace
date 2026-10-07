import Definitions.Def_RadGauss_RiskBound_rademacherComplexity
import Definitions.Def_RadGauss_Discrepancy_maxDiscrepancy
import Definitions.Def_RadGauss_Discrepancy_condSup

open MeasureTheory
open scoped ENNReal Pointwise

namespace RadGauss.Discrepancy

/-- **Lemma 3** (p. 465), first and second displays, for `n = 2m`:
`R_n(F)/2 − 2√(2/n) ≤ D_n(F) ≤ R_n(F) + 4√(2/n)`, and `R_n(F) − 4√(2/n) ≤ D_n(F)` when `F` is
closed under negation. Subtractions are moved to the other side to avoid truncated subtraction
in `ℝ≥0∞`. -/
theorem lemma_3 {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (m : ℕ) (hm : 0 < m) (F : Set (X → ℝ)) (hFne : F.Nonempty)
    (hFrange : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1)
    (hFmeas : ∀ f ∈ F, Measurable f)
    (hsup : ∀ σ : Fin (2 * m) → Bool,
      Measurable fun x : Fin (2 * m) → X => ⨆ f : F, ∑ i, RadGauss.RiskBound.signVal (σ i) * (f : X → ℝ) (x i)) :
    (RadGauss.RiskBound.rademacherComplexity μ (2 * m) F / 2
        ≤ ENNReal.ofReal (expectedMaxDiscrepancy μ m F)
          + ENNReal.ofReal (2 * Real.sqrt (2 / ((2 * m : ℕ) : ℝ))) ∧
      ENNReal.ofReal (expectedMaxDiscrepancy μ m F)
        ≤ RadGauss.RiskBound.rademacherComplexity μ (2 * m) F
          + ENNReal.ofReal (4 * Real.sqrt (2 / ((2 * m : ℕ) : ℝ)))) ∧
    ((∀ f ∈ F, -f ∈ F) →
      RadGauss.RiskBound.rademacherComplexity μ (2 * m) F
        ≤ ENNReal.ofReal (expectedMaxDiscrepancy μ m F)
          + ENNReal.ofReal (4 * Real.sqrt (2 / ((2 * m : ℕ) : ℝ)))) := by sorry

end RadGauss.Discrepancy

