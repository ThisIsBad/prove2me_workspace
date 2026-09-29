import Mathlib
import Definitions.Def_TraceEstimation_Shared_gaussianEstimator

namespace TraceEstimation.Gaussian

open MeasureTheory ProbabilityTheory Matrix

/-- Lemma 5.1 (Avron–Toledo, p. 8:7). For a symmetric `A`, the single-sample Gaussian
estimator `G_1 = zᵀ A z` is square integrable and unbiased, `E(G_1) = trace(A)`, and has
variance `Var(G_1) = 2‖A‖_F² = 2 ∑_{i,j} A_{ij}²`. The paper's remark that the lemma "also
applies when A is non-symmetric" is not part of the lemma and is false for the variance. -/
theorem single_sample_mean_variance {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsHermitian) :
    MemLp (Shared.gaussianEstimator A 1) 2 (Shared.gaussianSampleMeasure n 1) ∧
    ∫ ω, Shared.gaussianEstimator A 1 ω ∂(Shared.gaussianSampleMeasure n 1) = A.trace ∧
    variance (Shared.gaussianEstimator A 1) (Shared.gaussianSampleMeasure n 1) =
      2 * ∑ i : Fin n, ∑ j : Fin n, A i j ^ 2 := by sorry

end TraceEstimation.Gaussian
