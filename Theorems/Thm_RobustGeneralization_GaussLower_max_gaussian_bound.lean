import Mathlib
import Definitions.Def_RobustGeneralization_GaussLower_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RobustGeneralization.GaussLower

theorem max_gaussian_bound (d : ℕ) :
    ENNReal.ofReal (1 - 1 / (d : ℝ)) ≤
      stdGaussian (E d) {v | ∀ i, |v i| ≤ 2 * Real.sqrt (2 * Real.log d)} := by sorry

end RobustGeneralization.GaussLower
