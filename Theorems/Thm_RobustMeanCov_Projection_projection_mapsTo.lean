import Mathlib
import Definitions.Def_RobustMeanCov_Projection_MeanCovClass
import Definitions.Def_RobustMeanCov_Shared_MeanVarClass
open MeasureTheory Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace RobustMeanCov.Projection

/-- §2.1, justification of (4) (Popescu 2007, p. 100): the projected law of `x′R` has mean
`x′μ` and variance `x′Σx`. -/
theorem projection_mapsTo {n : ℕ} (μ x : EuclideanSpace ℝ (Fin n))
    (S : Matrix (Fin n) (Fin n) ℝ) :
    Set.MapsTo (fun P : Measure (EuclideanSpace ℝ (Fin n)) => P.map (fun R => ⟪x, R⟫))
      (MeanCovClass μ S) (RobustMeanCov.Shared.MeanVarClass ⟪x, μ⟫ (x.ofLp ⬝ᵥ S *ᵥ x.ofLp)) := by sorry

end RobustMeanCov.Projection
