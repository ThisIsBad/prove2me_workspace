import Mathlib
import Definitions.Def_TSPHeuristics_Shared_TSPModel
import Definitions.Def_TSPHeuristics_KOpt_CircleInstance
import Definitions.Def_TSPHeuristics_KOpt_UnitEdgeCount

namespace TSPHeuristics.KOpt

theorem theorem_6_proof_shortest_even_tour (n : ℕ) (hn : 6 ≤ n) :
    (∀ (τ : Equiv.Perm (Fin n)) (e e' : Fin n),
        unitCount τ e = 0 → unitCount τ e' = 0 → e = e') ∧
      (∀ τ : Equiv.Perm (Fin n), (∀ e : Fin n, Even (unitCount τ e)) →
        TSPHeuristics.Shared.cycleLength (cycDist n) (circleSubtour n n) ≤ TSPHeuristics.Shared.tourLength (cycDist n) τ) ∧
      (∀ τ : Equiv.Perm (Fin n),
        TSPHeuristics.Shared.tourLength (cycDist n) τ < TSPHeuristics.Shared.cycleLength (cycDist n) (circleSubtour n n) →
          ∀ e : Fin n, Odd (unitCount τ e)) := by sorry

end TSPHeuristics.KOpt
