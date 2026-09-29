import Mathlib
import Definitions.Def_RobustMeanCov_Projection_MeanCovClass
import Definitions.Def_RobustMeanCov_Shared_MeanVarClass
open MeasureTheory Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace RobustMeanCov.Projection

/-- Appendix, proof of Theorem 1, (1) (Popescu 2007, p. 109): standardizing a law with mean `m`
and variance `v > 0` by `z = v^{-1/2}(r - m)` gives a law with mean 0 and variance 1. -/
theorem standardize_mem (m v : ℝ) (hv : 0 < v) (ν : Measure ℝ) (hν : ν ∈ RobustMeanCov.Shared.MeanVarClass m v) :
    ν.map (fun r => v ^ (-(1 / 2 : ℝ)) * (r - m)) ∈ RobustMeanCov.Shared.MeanVarClass 0 1 := by sorry

end RobustMeanCov.Projection
