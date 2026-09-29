import Mathlib
import Definitions.Def_PorteusSS_Functions

open MeasureTheory Filter Topology Set

namespace PorteusSS

/-- Lemma 9 (p. 424). For `K ≥ 0`: if `f ∈ C_a(K)` for some `a`, then `f` is quasi-`K`-convex
on `ℝ`, piecewise continuous, PF-integrable and `f x → ∞` as `|x| → ∞`; conversely these four
properties imply `f ∈ C_a(K)` for some `a ∈ ℝ`. -/
theorem CaK_iff_quasiKConvex (K : ℝ) (hK : 0 ≤ K) (f : ℝ → ℝ) :
    (∀ a : ℝ, CaK a K f →
      QuasiKConvexOn f K univ ∧ PiecewiseContinuousOn f univ ∧ PFIntegrable f ∧
        Tendsto f (cocompact ℝ) atTop) ∧
    (QuasiKConvexOn f K univ ∧ PiecewiseContinuousOn f univ ∧ PFIntegrable f ∧
        Tendsto f (cocompact ℝ) atTop → ∃ a : ℝ, CaK a K f) := by sorry

end PorteusSS
