import Mathlib
import Definitions.Def_CriticalPath_CostCurve_ProjectNetwork
import Definitions.Def_CriticalPath_CostCurve_earliest
import Definitions.Def_CriticalPath_CostCurve_JobData
import Definitions.Def_CriticalPath_CostCurve_Schedule

namespace CriticalPath.CostCurve

/-- Kelley–Walker (1959), §3, p. 165: within the limits of most interest,
`tₙ⁽⁰⁾(d) ≤ lam ≤ tₙ⁽⁰⁾(D)`, some minimum cost schedule `(y, t)` for `lam` has earliest project
completion time `tₙ⁽⁰⁾(y) = lam`. -/
theorem exists_optimal_earliest_eq {n : ℕ} (N : ProjectNetwork n) (J : JobData N) (lam : ℝ)
    (hlo : earliest N J.d (Fin.last n) ≤ lam) (hhi : lam ≤ earliest N J.D (Fin.last n)) :
    ∃ (y : Fin (n + 1) → Fin (n + 1) → ℝ) (t : Fin (n + 1) → ℝ),
      IsOptimalSchedule J lam y t ∧ earliest N y (Fin.last n) = lam := by sorry

end CriticalPath.CostCurve

