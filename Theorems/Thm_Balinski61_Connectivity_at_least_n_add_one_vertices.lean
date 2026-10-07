import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Balinski61_Connectivity_Polyhedron

open scoped RealInnerProductSpace

namespace Balinski61.Connectivity

theorem at_least_n_add_one_vertices (n m : ℕ)
    (a : Fin m → EuclideanSpace ℝ (Fin n)) (b : Fin m → ℝ)
    (hS : StandingAssumptions a b) :
    (n : ℕ∞) + 1 ≤ (Set.extremePoints ℝ (Hirsch.Hpoly a b)).encard := by sorry

end Balinski61.Connectivity

