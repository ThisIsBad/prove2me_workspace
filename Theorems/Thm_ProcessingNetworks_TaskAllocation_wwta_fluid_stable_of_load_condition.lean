import Mathlib
import Definitions.Def_ProcessingNetworks_TaskAllocation_TaskAllocationModel
import Definitions.Def_ProcessingNetworks_TaskAllocation_FluidModel

namespace ProcessingNetworks.TaskAllocation

/-- Theorem 11.6, Dai & Harrison p. 220 (PDF p. 236) — the goal theorem of this mission: suppose
there exists an `I`-vector `λ = (λℓk) ≥ 0` satisfying (11.4) and (11.5). Then the WWTA fluid model,
defined by equations (11.11)-(11.16), is stable. (The book's own further sentence, "thus, by
Theorem 11.5 above, the task allocation model itself is stable under the WWTA routing policy," is
Theorem 11.5 applied to this conclusion, not new content of Theorem 11.6 itself, and is not
restated here — matching how mission IX's goal theorem states only the fluid-stability conclusion
proper.) -/
theorem wwta_fluid_stable_of_load_condition
    {L K : ℕ} [Nonempty (Fin K)] (dat : TaskAllocationData L K)
    (hload : ∃ lam : Fin L → Fin K → ℝ, (∀ ℓ k, 0 ≤ lam ℓ k) ∧
      (∀ ℓ, ∑ k, lam ℓ k = dat.nu ℓ) ∧ (∀ k, ∑ ℓ, dat.m ℓ k * lam ℓ k < 1)) :
    WWTAFluidStable dat := by sorry

end ProcessingNetworks.TaskAllocation
