import Mathlib
import Definitions.Def_CachonCoord_TwoLocation_Model

open MeasureTheory

namespace CachonCoord.TwoLocation

/-- §6.8.4, p. 83, Eq. (38). The equation `∫_0^∞ c'(s̄ − x) f_s(x) dx = 0` has exactly one
solution `s̄`; it is equivalent to `Pr(D_r + D_s ≤ s̄) = β/(h_r + β)` for independent `D_r`,
`D_s` (the law of `D_r + D_s` being the convolution of the two laws); and every optimal policy
`{s̃²_r, s̃²_s}` with `s̃²_s ≤ 0` satisfies `s̃²_r + s̃²_s = s̄`. -/
theorem eq_38 (M : Model) :
    (∃! sbar : ℝ, ∫ x, M.cDeriv (sbar - x) ∂M.lawS = 0) ∧
    (∀ s : ℝ, ∫ x, M.cDeriv (s - x) ∂M.lawS = 0 ↔
      (M.lawR.conv M.lawS).real (Set.Iic s) = M.beta / (M.hr + M.beta)) ∧
    (∀ sbar : ℝ, ∫ x, M.cDeriv (sbar - x) ∂M.lawS = 0 →
      ∀ sr ss : ℝ, IsMinOn (fun p : ℝ × ℝ => M.Pi p.1 p.2) Set.univ (sr, ss) → ss ≤ 0 →
        sr + ss = sbar) := by sorry

end CachonCoord.TwoLocation

