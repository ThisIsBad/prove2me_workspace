import Definitions.Def_RadGauss_RiskBound_rademacherComplexity
import Definitions.Def_RadGauss_Discrepancy_maxDiscrepancy
import Definitions.Def_RadGauss_Discrepancy_condSup

open MeasureTheory
open scoped ENNReal Pointwise

namespace RadGauss.Discrepancy

/-- Appendix A, p. 479, last display: for `N = Σ_i σ_i` (so `E N = 0`) and `n = 2m`,
`|E s(N) − s(E N)| ≤ E|s(N) − s(E N)| ≤ 4 √(2/n)`. Expectations over uniform signs are averages
over all `2^n` sign vectors. -/
theorem expect_condSup_deviation {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (m : ℕ) (hm : 0 < m) (F : Set (X → ℝ)) (hFne : F.Nonempty)
    (hFrange : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1)
    (hFmeas : ∀ f ∈ F, Measurable f)
    (hsup : ∀ σ : Fin (2 * m) → Bool,
      Measurable fun x : Fin (2 * m) → X => ⨆ f : F, ∑ i, RadGauss.RiskBound.signVal (σ i) * (f : X → ℝ) (x i)) :
    |((2 : ℝ) ^ (2 * m))⁻¹ * ∑ σ : Fin (2 * m) → Bool, condSup μ (2 * m) F (sumSign σ)
        - condSup μ (2 * m) F 0|
      ≤ ((2 : ℝ) ^ (2 * m))⁻¹ * ∑ σ : Fin (2 * m) → Bool,
          |condSup μ (2 * m) F (sumSign σ) - condSup μ (2 * m) F 0| ∧
    ((2 : ℝ) ^ (2 * m))⁻¹ * ∑ σ : Fin (2 * m) → Bool,
          |condSup μ (2 * m) F (sumSign σ) - condSup μ (2 * m) F 0|
      ≤ 4 * Real.sqrt (2 / ((2 * m : ℕ) : ℝ)) := by sorry

end RadGauss.Discrepancy

