import Mathlib
import Definitions.Def_Disjunctive_RayCGLP_Basic

namespace Disjunctive.RayCGLP

/-- Corollary 10.4 (Balas §10.6, p. 139, [32]): for `y := x*-x̄` with `x*∈P_Q`, `(CGLP)_y` (defined
w.r.t. `P_D`) has an optimal solution `(α̃,β̃)` such that (i) `α̃x̄<β̃`, and (ii) `α̃x=β̃` is a
supporting hyperplane of `P_Q` whose intersection with the line through `x̄,x*` at parameter
`t∈(0,1]` (i.e. the point `x̄+t(x*-x̄)`, `t=1` being `x*` itself) is the greatest such `t` —
matching "the point closest to `x*`" on the segment `(x̄,x*]`.

**Corrects a source typo** (confirmed against the figure caption "Fig. 10.3 `y = x*-x̄`" in the
same section, immediately following this corollary): the printed corollary reads "`y:=x̄` for some
`x*∈P_Q`," omitting "`x*−`" before "`x̄`"; see `MODERATION_NOTES.md`. On the page `P_Q` and `P_D` are the same set, `cl conv F`; carrying them as two unrelated
parameters leaves the supporting-hyperplane claim about a set the optimum knows nothing of. -/
theorem ray_normalization_geometry {n : ℕ} (PD : Set (Fin n → ℝ)) (hPDconv : Convex ℝ PD)
    (hPDclosed : IsClosed PD) (xbar xstar : Fin n → ℝ)
    (hxstar : xstar ∈ PD) :
    ∃ alphaT betaT, IsCGLPYOptimal PD (xstar - xbar) xbar alphaT betaT ∧
      dotProduct alphaT xbar < betaT ∧ (∀ x ∈ PD, betaT ≤ dotProduct alphaT x) ∧
      ∃ t : ℝ, IsGreatest
        {t' : ℝ | t' ∈ Set.Ioc (0 : ℝ) 1 ∧
          dotProduct alphaT (xbar + t' • (xstar - xbar)) = betaT} t := by sorry

end Disjunctive.RayCGLP

