import Mathlib
import Definitions.Def_RobustGeneralization_GaussLower_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RobustGeneralization.GaussLower

theorem psi_lower_bound {d : ℕ} (f : E d → Bool) (m : E d) (s ε : ℝ) (hs : 0 < s)
    (hm : ∀ i, |m i| ≤ ε) :
    (1 / 2 : ℝ≥0∞) ≤ robustErr (gaussModel m s) f ε := by sorry

end RobustGeneralization.GaussLower
