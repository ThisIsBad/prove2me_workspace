import Mathlib
import Definitions.Def_TSPHeuristics_KOpt_UnitEdgeCount

namespace TSPHeuristics.KOpt

theorem theorem_6_proof_tour_odd_or_even (n : ℕ) (hn : 3 ≤ n) (τ : Equiv.Perm (Fin n)) :
    (∀ e : Fin n, Even (unitCount τ e)) ∨ (∀ e : Fin n, Odd (unitCount τ e)) := by sorry

end TSPHeuristics.KOpt
