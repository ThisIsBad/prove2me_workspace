import Mathlib
import Definitions.Def_Disjunctive_SequentialConvex_Basic

namespace Disjunctive.SequentialConvex

/-- Theorem 3.3 (Balas §3.2, p. 46): `F_{j-1}` and `D_j` satisfy the sequential-convexifiability
relation (3.5) if and only if they satisfy the constraint boundary condition (3.6): every point
where a segment from `F_{j-1} ∩ D̄_j` to `F_{j-1} ∩ D_j` crosses the (relative) boundary of `D̄_j`
lies in `conv(F_{j-1} ∩ D_j)`. -/
theorem constraint_boundary_condition {n : ℕ} (Fjm1 : Set (Fin n → ℝ)) {Qj : Type*} [Fintype Qj]
    (d : Qj → Fin n → ℝ) (d0 : Qj → ℝ) :
    (convexHull ℝ (convexHull ℝ Fjm1 ∩ Dj d d0) = convexHull ℝ (Fjm1 ∩ Dj d d0)) ↔
      (∀ x ∈ Fjm1 ∩ Dbarj d d0, ∀ y ∈ Fjm1 ∩ Dj d d0,
        segment ℝ x y ∩ intrinsicFrontier ℝ (Dbarj d d0) ⊆ convexHull ℝ (Fjm1 ∩ Dj d d0)) := by sorry

end Disjunctive.SequentialConvex

