import Mathlib
import Definitions.Def_RuralPostman_NPC_Reductions

namespace RuralPostman.NPC

theorem claim_undirected_backward {v : ℕ} (adj : Fin v → Fin v → Bool) (hs : IsSymm adj)
    (hv : 3 ≤ v) (hG : (urpOfGraph adj).RPYes false) :
    SchedComplexity.NoWait.HasHamiltonCircuit adj := by sorry

end RuralPostman.NPC

