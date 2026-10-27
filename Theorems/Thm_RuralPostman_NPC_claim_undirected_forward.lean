import Mathlib
import Definitions.Def_RuralPostman_NPC_Reductions

namespace RuralPostman.NPC

theorem claim_undirected_forward {v : ℕ} (adj : Fin v → Fin v → Bool) (hs : IsSymm adj)
    (hv : 3 ≤ v) (hH : SchedComplexity.NoWait.HasHamiltonCircuit adj) :
    ∃ τ : List (urpOfGraph adj).Traversal, (urpOfGraph adj).IsTour false τ ∧
      (∀ e, (urpOfGraph adj).IsRequired e → τ.countP (fun t => t.1 = e) = 2) ∧
      τ.countP (fun t => ¬ (urpOfGraph adj).IsRequired t.1) = v ∧
      (∀ e, ¬ (urpOfGraph adj).IsRequired e → τ.countP (fun t => t.1 = e) ≤ 1) ∧
      (urpOfGraph adj).tourWeight τ = v := by sorry

end RuralPostman.NPC

