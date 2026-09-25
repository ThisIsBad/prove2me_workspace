import Definitions.Def_SupplyChainTheory_tsp

open Classical

namespace SupplyChainTheory

theorem revised_cost_identities {n : ℕ} (c : Fin n → Fin n → ℝ) (hc : IsMetric c) (hn : 3 ≤ n)
    (lam : Fin n → ℝ) :
    (∀ τ : Equiv.Perm (Fin n), tourLength (revisedCost c lam) τ = tourLength c τ + 2 * ∑ i, lam i)
      ∧ (∀ τ : Equiv.Perm (Fin n), IsMinOn (tourLength c) Set.univ τ →
          IsMinOn (tourLength (revisedCost c lam)) Set.univ τ)
      ∧ ∀ (r : Fin n) (G : SimpleGraph (Fin n)), Is1Tree r G →
          graphWeight (revisedCost c lam) G = graphWeight c G + ∑ i, G.degree i * lam i := by sorry

end SupplyChainTheory
