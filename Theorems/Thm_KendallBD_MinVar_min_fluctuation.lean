import Mathlib
import Definitions.Def_KendallBD_MinVar_Setting

namespace KendallBD.MinVar

/-- Kendall (1948), (56), p. 12: the unique rate pair minimizing variance
simultaneously at all nonnegative times for a prescribed mean. -/
theorem min_fluctuation (nbar : ℝ → ℝ)
    (hn : ContDiff ℝ 1 nbar) (hpos : ∀ t, 0 < nbar t) (h0 : nbar 0 = 1) :
    (Admissible (lamStar nbar) (muStar nbar) ∧
      HasMean (lamStar nbar) (muStar nbar) nbar) ∧
    (∀ lam mu : ℝ → ℝ, Admissible lam mu → HasMean lam mu nbar →
      ∀ t : ℝ, 0 ≤ t →
        fluct (lamStar nbar) (muStar nbar) t ≤ fluct lam mu t) ∧
    (∀ lam mu : ℝ → ℝ, Admissible lam mu → HasMean lam mu nbar →
      (∀ t : ℝ, 0 ≤ t →
        fluct lam mu t = fluct (lamStar nbar) (muStar nbar) t) →
      ∀ t : ℝ, 0 ≤ t →
        lam t = lamStar nbar t ∧ mu t = muStar nbar t) := by sorry

end KendallBD.MinVar

