import Mathlib
import Definitions.Def_KendallBD_MinVar_Setting

namespace KendallBD.MinVar

/-- Kendall (1948), (55), p. 11. -/
theorem rate_difference (nbar lam mu : ℝ → ℝ)
    (hn : ContDiff ℝ 1 nbar) (hpos : ∀ t, 0 < nbar t) (h0 : nbar 0 = 1)
    (hadm : Admissible lam mu) (hmean : HasMean lam mu nbar) :
    ∀ t : ℝ, 0 ≤ t → lam t - mu t = growth nbar t := by sorry

end KendallBD.MinVar

