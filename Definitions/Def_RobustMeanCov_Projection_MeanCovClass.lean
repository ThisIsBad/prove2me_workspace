import Mathlib
open MeasureTheory

namespace RobustMeanCov.Projection

/-- The class `𝕄ⁿ_(μ,Σ)` (Popescu 2007, p. 98 and p. 100): probability measures `P` on `ℝⁿ`
(modelled as `EuclideanSpace ℝ (Fin n)` with its Borel σ-algebra) whose coordinates have finite
second moments, with mean vector `μ` and covariance matrix `S` (the paper's `Σ`). -/
def MeanCovClass {n : ℕ} (μ : EuclideanSpace ℝ (Fin n)) (S : Matrix (Fin n) (Fin n) ℝ) :
    Set (Measure (EuclideanSpace ℝ (Fin n))) :=
  {P | IsProbabilityMeasure P ∧
    (∀ i, MemLp (fun R : EuclideanSpace ℝ (Fin n) => R i) 2 P) ∧
    (∀ i, ∫ R, R i ∂P = μ i) ∧
    (∀ i j, ∫ R, (R i - μ i) * (R j - μ j) ∂P = S i j)}

end RobustMeanCov.Projection
