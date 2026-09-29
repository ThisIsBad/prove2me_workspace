import Mathlib
import Definitions.Def_TSPHeuristics_Shared_TSPModel
import Definitions.Def_TSPHeuristics_KOpt_CircleInstance
import Definitions.Def_TSPHeuristics_KOpt_UnitEdgeCount

namespace TSPHeuristics.KOpt

theorem eq_7_4_tourLength_eq_sum_unitCount (n : ℕ) (τ : Equiv.Perm (Fin n)) :
    TSPHeuristics.Shared.tourLength (cycDist n) τ = ∑ e : Fin n, (unitCount τ e : ℝ) := by sorry

end TSPHeuristics.KOpt
