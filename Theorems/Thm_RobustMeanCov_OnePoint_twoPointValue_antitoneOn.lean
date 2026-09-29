import Mathlib
import Definitions.Def_RobustMeanCov_OnePoint_twoPointValue

namespace RobustMeanCov.OnePoint

theorem twoPointValue_antitoneOn (u : ℝ → ℝ) (hu : Differentiable ℝ u)
    (hconv : ConvexOn ℝ Set.univ (deriv u)) (m s : ℝ) (hs : 0 < s) :
    AntitoneOn (twoPointValue u m s) (Set.Ioo 0 1) := by sorry

end RobustMeanCov.OnePoint
