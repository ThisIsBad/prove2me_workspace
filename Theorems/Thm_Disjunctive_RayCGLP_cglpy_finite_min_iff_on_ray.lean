import Mathlib
import Definitions.Def_Disjunctive_RayCGLP_Basic

namespace Disjunctive.RayCGLP

/-- Theorem 10.2 (Balas §10.6, p. 138, [32]): if `(CGLP)_y` is feasible, it has a finite minimum
if and only if `x̄+yλ ∈ P_D` for some `λ ∈ ℝ`. `P_D` is the closed convex hull of the disjunctive set, as on the page; the separation
argument of the proof needs it (`P_D = {(3,1), (3,-1)}`, `x̄ = 0`, `y = (1,0)` refutes the
statement for an arbitrary set). -/
theorem cglpy_finite_min_iff_on_ray {n : ℕ} (PD : Set (Fin n → ℝ)) (hPDconv : Convex ℝ PD)
    (hPDclosed : IsClosed PD) (y xbar : Fin n → ℝ)
    (hfeas : ∃ α β, IsCGLPYFeasible PD y α β) :
    CGLPYHasFiniteMin PD y xbar ↔ ∃ lam : ℝ, xbar + lam • y ∈ PD := by sorry

end Disjunctive.RayCGLP

