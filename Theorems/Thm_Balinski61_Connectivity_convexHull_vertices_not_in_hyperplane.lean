import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Balinski61_Connectivity_Polyhedron

open scoped RealInnerProductSpace

namespace Balinski61.Connectivity

theorem convexHull_vertices_not_in_hyperplane (n m : ℕ)
    (a : Fin m → EuclideanSpace ℝ (Fin n)) (b : Fin m → ℝ)
    (hS : StandingAssumptions a b) :
    (Set.extremePoints ℝ (Hirsch.Hpoly a b)).Finite ∧
      convexHull ℝ (Set.extremePoints ℝ (Hirsch.Hpoly a b)) = Hirsch.Hpoly a b ∧
      ∀ (c : EuclideanSpace ℝ (Fin n)) (d : ℝ), c ≠ 0 →
        ∃ x ∈ Hirsch.Hpoly a b, ⟪c, x⟫ ≠ d := by sorry

end Balinski61.Connectivity

