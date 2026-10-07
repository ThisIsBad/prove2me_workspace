import Definitions.Def_RadGauss_RiskBound_rademacherComplexity
import Definitions.Def_RadGauss_Discrepancy_maxDiscrepancy
import Definitions.Def_RadGauss_Discrepancy_condSup

open MeasureTheory
open scoped ENNReal Pointwise

namespace RadGauss.Discrepancy

/-- Appendix A, p. 479, first display: `R_n(F) ≥ E s(Σ_i σ_i)`, with equality when `F` is closed
under negation. The expectation over uniform signs is the average over all `2^n` sign vectors. -/
theorem rademacher_ge_expect_condSup {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (n : ℕ) (hn : 0 < n) (F : Set (X → ℝ)) (hFne : F.Nonempty)
    (hFrange : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1)
    (hFmeas : ∀ f ∈ F, Measurable f)
    (hsup : ∀ σ : Fin n → Bool,
      Measurable fun x : Fin n → X => ⨆ f : F, ∑ i, RadGauss.RiskBound.signVal (σ i) * (f : X → ℝ) (x i)) :
    ENNReal.ofReal (((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool, condSup μ n F (sumSign σ))
        ≤ RadGauss.RiskBound.rademacherComplexity μ n F ∧
      ((∀ f ∈ F, -f ∈ F) →
        RadGauss.RiskBound.rademacherComplexity μ n F =
          ENNReal.ofReal (((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool, condSup μ n F (sumSign σ))) := by sorry

end RadGauss.Discrepancy

