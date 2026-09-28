import Mathlib
import Definitions.Def_CriticalPath_CostCurve_ProjectNetwork

namespace CriticalPath.CostCurve

variable {n : ℕ}

/-- Job data of Kelley–Walker (1959), §3, p. 164: for every job `(i, j) ∈ P` a crash duration
`dᵢⱼ` and a normal duration `Dᵢⱼ` with `0 ≤ dᵢⱼ ≤ Dᵢⱼ` (the constant part of (5)), and a linear
job cost `aᵢⱼ yᵢⱼ + bᵢⱼ` with `aᵢⱼ ≤ 0`, `bᵢⱼ ≥ 0` ((6)). Values off `P` are never read. -/
structure JobData (N : ProjectNetwork n) where
  /-- Crash durations `dᵢⱼ`. -/
  d : Fin (n + 1) → Fin (n + 1) → ℝ
  /-- Normal durations `Dᵢⱼ`. -/
  D : Fin (n + 1) → Fin (n + 1) → ℝ
  /-- Slopes `aᵢⱼ` of the linear job costs. -/
  a : Fin (n + 1) → Fin (n + 1) → ℝ
  /-- Intercepts `bᵢⱼ` of the linear job costs. -/
  b : Fin (n + 1) → Fin (n + 1) → ℝ
  crash_nonneg : ∀ e ∈ N.P, 0 ≤ d e.1 e.2
  crash_le_normal : ∀ e ∈ N.P, d e.1 e.2 ≤ D e.1 e.2
  slope_nonpos : ∀ e ∈ N.P, a e.1 e.2 ≤ 0
  intercept_nonneg : ∀ e ∈ N.P, 0 ≤ b e.1 e.2

/-- Project (direct) cost (7), p. 164: `∑_{(i,j) ∈ P} (aᵢⱼ yᵢⱼ + bᵢⱼ)`. -/
def projectCost {N : ProjectNetwork n} (J : JobData N) (y : Fin (n + 1) → Fin (n + 1) → ℝ) : ℝ :=
  ∑ e ∈ N.P, (J.a e.1 e.2 * y e.1 e.2 + J.b e.1 e.2)

end CriticalPath.CostCurve
