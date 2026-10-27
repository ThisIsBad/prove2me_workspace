import Mathlib
import Definitions.Def_RuralPostman_NPC_Reductions

namespace RuralPostman.NPC

theorem claim_directed {v : ℕ} (adj : Fin v → Fin v → Bool) (hv : v ≠ 1) :
    SchedComplexity.NoWait.HasHamiltonCircuit adj ↔ (drpOfGraph adj).RPYes true := by sorry

end RuralPostman.NPC

