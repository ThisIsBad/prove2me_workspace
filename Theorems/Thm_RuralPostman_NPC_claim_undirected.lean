import Mathlib
import Definitions.Def_RuralPostman_NPC_Reductions

namespace RuralPostman.NPC

theorem claim_undirected {v : ℕ} (adj : Fin v → Fin v → Bool) (hs : IsSymm adj) (hv : 3 ≤ v) :
    SchedComplexity.NoWait.HasHamiltonCircuit adj ↔ (urpOfGraph adj).RPYes false := by sorry

end RuralPostman.NPC

