import Mathlib
import Definitions.Def_RobustMeanCov_Projection_MeanCovClass
import Definitions.Def_RobustMeanCov_Shared_MeanVarClass
open MeasureTheory Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace RobustMeanCov.Projection

/-- Appendix, proof of Theorem 1 (Popescu 2007, pp. 109–110): for a unit vector `y` and a law
`z ∼ (0, 1)`, there is a random vector `Z ∼ (0, Iₙ)` with `y′Z` distributed as `z`. -/
theorem exists_isotropic_lift {n : ℕ} (y : EuclideanSpace ℝ (Fin n)) (hy : ⟪y, y⟫ = 1)
    (ζ : Measure ℝ) (hζ : ζ ∈ RobustMeanCov.Shared.MeanVarClass 0 1) :
    ∃ Q ∈ MeanCovClass (0 : EuclideanSpace ℝ (Fin n)) (1 : Matrix (Fin n) (Fin n) ℝ),
      Q.map (fun Z => ⟪y, Z⟫) = ζ := by sorry

end RobustMeanCov.Projection

