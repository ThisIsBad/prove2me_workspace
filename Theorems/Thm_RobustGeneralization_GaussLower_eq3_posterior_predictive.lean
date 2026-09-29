import Mathlib
import Definitions.Def_RobustGeneralization_GaussLower_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RobustGeneralization.GaussLower

theorem eq3_posterior_predictive {d : ℕ} (m : E d) (s σ : ℝ) (hs : 0 < s) (hσ : 0 < σ) :
    (gaussVec m s).bind (fun θ => gaussModel θ σ) =
      gaussModel m (Real.sqrt (s ^ 2 + σ ^ 2)) := by sorry

end RobustGeneralization.GaussLower
