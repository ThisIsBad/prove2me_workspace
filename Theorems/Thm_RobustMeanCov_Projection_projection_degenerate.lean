import Mathlib
import Definitions.Def_RobustMeanCov_Projection_MeanCovClass
import Definitions.Def_RobustMeanCov_Shared_MeanVarClass
open MeasureTheory Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace RobustMeanCov.Projection

/-- Appendix, proof of Theorem 1, first sentence (Popescu 2007, p. 109): if `x′Σx = 0`, then
`x′R ≡ x′μ` almost surely for every law `R ∼ (μ, Σ)`. -/
theorem projection_degenerate {n : ℕ} (μ x : EuclideanSpace ℝ (Fin n))
    (S : Matrix (Fin n) (Fin n) ℝ) (hq : x.ofLp ⬝ᵥ S *ᵥ x.ofLp = 0)
    (P : Measure (EuclideanSpace ℝ (Fin n))) (hP : P ∈ MeanCovClass μ S) :
    ∀ᵐ R ∂P, ⟪x, R⟫ = ⟪x, μ⟫ := by sorry

end RobustMeanCov.Projection
