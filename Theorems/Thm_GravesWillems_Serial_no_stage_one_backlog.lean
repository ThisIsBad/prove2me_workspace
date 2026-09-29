import Mathlib
import Definitions.Def_GravesWillems_Serial_backlog
import Definitions.Def_GravesWillems_Serial_programP

namespace GravesWillems.Serial

/-- Eq. (A3) of Graves–Willems 2000 (Appendix, p. 81), sufficiency: if the demand path never
exceeds the demand bound, `d(a, a + s] ≤ D(s)` for every time `a` and every number of periods `s`,
and the base stocks satisfy the constraints (A3), then stage 1 never has a backlog:
`Q₁(t) = 0` for all `t`. -/
theorem no_stage_one_backlog (N : ℕ) (T : ℕ → ℕ) (D : ℕ → ℝ) (B : ℕ → ℝ) (d : ℤ → ℝ)
    (hdD : ∀ (a : ℤ) (s : ℕ), windowDemand d a (a + (s : ℤ)) ≤ D s)
    (hB : ServiceConstraints N T D B) (t : ℤ) :
    backlog N T B d 1 t = 0 := by sorry

end GravesWillems.Serial
