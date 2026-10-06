import Mathlib
import Definitions.Def_PhiDivRobust_Barrier_perspective

namespace PhiDivRobust.Barrier

/-- The interior of the set (34) `{y f(s/y) ≤ z, s ≥ 0, y ≥ 0}` on which the barrier (35) is finite:
the points `(s, y, z)` with `s > 0`, `y > 0` and `y f(s/y) < z`. -/
def barrierDomain (f : ℝ → ℝ) : Set (ℝ × ℝ × ℝ) :=
  {p | 0 < p.1 ∧ 0 < p.2.1 ∧ perspective f (p.1, p.2.1) < p.2.2}

/-- The logarithmic barrier (35): `φ_B(s, y, z) = -ln(z - y f(s/y)) - ln s - ln y`. -/
noncomputable def logBarrier (f : ℝ → ℝ) (p : ℝ × ℝ × ℝ) : ℝ :=
  -Real.log (p.2.2 - perspective f (p.1, p.2.1)) - Real.log p.1 - Real.log p.2.1

end PhiDivRobust.Barrier
