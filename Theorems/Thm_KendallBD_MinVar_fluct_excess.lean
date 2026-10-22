import Mathlib
import Definitions.Def_KendallBD_MinVar_Setting

namespace KendallBD.MinVar

/-- The nonnegative excess term in Kendall's minimum-fluctuation argument,
§6, p. 12, following the variance decomposition. -/
theorem fluct_excess (nbar lam mu : ℝ → ℝ)
    (hn : ContDiff ℝ 1 nbar) (hpos : ∀ t, 0 < nbar t) (h0 : nbar 0 = 1)
    (hadm : Admissible lam mu) (hmean : HasMean lam mu nbar) :
    ∀ t : ℝ, 0 ≤ t →
      fluct lam mu t = fluct (lamStar nbar) (muStar nbar) t +
        2 * Real.exp (-2 * KendallBD.Sol.rho lam mu t) *
          ∫ τ in (0 : ℝ)..t,
            Real.exp (KendallBD.Sol.rho lam mu τ) * min (lam τ) (mu τ) := by sorry

end KendallBD.MinVar

