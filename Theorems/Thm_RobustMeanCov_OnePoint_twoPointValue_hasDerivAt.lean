import Mathlib
import Definitions.Def_RobustMeanCov_OnePoint_twoPointValue

namespace RobustMeanCov.OnePoint

theorem twoPointValue_hasDerivAt (u : ℝ → ℝ) (hu : Differentiable ℝ u) (m s p : ℝ)
    (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun q : ℝ => twoPointValue u m s q)
      (u (m + Real.sqrt ((1 - p) / p) * s) - u (m - Real.sqrt (p / (1 - p)) * s)
        - ((m + Real.sqrt ((1 - p) / p) * s) - (m - Real.sqrt (p / (1 - p)) * s))
          * (deriv u (m + Real.sqrt ((1 - p) / p) * s)
              + deriv u (m - Real.sqrt (p / (1 - p)) * s)) / 2) p := by sorry

end RobustMeanCov.OnePoint
