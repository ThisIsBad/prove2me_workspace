import Mathlib
import Definitions.Def_RuralPostman_NPC_Reductions

namespace RuralPostman.NPC

theorem claim_undirected_count {v : ℕ} (adj : Fin v → Fin v → Bool) (hs : IsSymm adj)
    (hv : 3 ≤ v) (τ : List (urpOfGraph adj).Traversal) (hτ : (urpOfGraph adj).IsTour false τ)
    (hw : (urpOfGraph adj).tourWeight τ ≤ (urpOfGraph adj).k) :
    τ.countP (fun t => ¬ (urpOfGraph adj).IsRequired t.1) = v ∧
      ∀ e, ¬ (urpOfGraph adj).IsRequired e → τ.countP (fun t => t.1 = e) ≤ 1 := by sorry

end RuralPostman.NPC

