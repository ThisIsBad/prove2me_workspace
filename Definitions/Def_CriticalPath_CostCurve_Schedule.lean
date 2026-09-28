import Mathlib
import Definitions.Def_CriticalPath_CostCurve_ProjectNetwork
import Definitions.Def_CriticalPath_CostCurve_JobData

namespace CriticalPath.CostCurve

variable {n : ℕ} {N : ProjectNetwork n}

/-- A schedule for the completion time `lam` (the paper's `λ`), Kelley–Walker (1959), p. 165:
durations `y` and event times `t` satisfying
(5) `dᵢⱼ ≤ yᵢⱼ ≤ Dᵢⱼ` for `(i, j) ∈ P`, (8) `yᵢⱼ ≤ tⱼ − tᵢ` for `(i, j) ∈ P`, and
(9) `t₀ = 0`, `tₙ = λ`. -/
def IsSchedule (J : JobData N) (lam : ℝ) (y : Fin (n + 1) → Fin (n + 1) → ℝ)
    (t : Fin (n + 1) → ℝ) : Prop :=
  (∀ e ∈ N.P, J.d e.1 e.2 ≤ y e.1 e.2 ∧ y e.1 e.2 ≤ J.D e.1 e.2) ∧
  (∀ e ∈ N.P, y e.1 e.2 ≤ t e.2 - t e.1) ∧
  t 0 = 0 ∧ t (Fin.last n) = lam

/-- The costs (7) of all schedules for `lam`: the objective values of the linear program
"minimize (7) subject to (5), (8), (9)". -/
def costSet (J : JobData N) (lam : ℝ) : Set ℝ :=
  {c | ∃ y t, IsSchedule J lam y t ∧ c = projectCost J y}

/-- The feasible completion times `Λ`: the `lam` for which some schedule exists. -/
def feasibleDurations (J : JobData N) : Set ℝ :=
  {lam | ∃ y t, IsSchedule J lam y t}

/-- A minimum cost schedule for `lam`: a schedule whose cost (7) is no larger than the cost of
any other schedule for `lam`. -/
def IsOptimalSchedule (J : JobData N) (lam : ℝ) (y : Fin (n + 1) → Fin (n + 1) → ℝ)
    (t : Fin (n + 1) → ℝ) : Prop :=
  IsSchedule J lam y t ∧ ∀ y' t', IsSchedule J lam y' t' → projectCost J y ≤ projectCost J y'

end CriticalPath.CostCurve
