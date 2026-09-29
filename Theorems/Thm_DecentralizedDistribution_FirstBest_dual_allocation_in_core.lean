import Mathlib
import Definitions.Def_Supermodularity_Cooperative_Core
import Definitions.Def_DecentralizedDistribution_FirstBest_System
import Definitions.Def_DecentralizedDistribution_FirstBest_DualPrices

open Supermodularity.Cooperative

namespace DecentralizedDistribution.FirstBest

/-- Theorem 4.1 (p. 358). For a nonnegative profile `[Z]` (all inventory claimed) and any demand
realization `D⃗`: the core of SAG([Z], D⃗) is nonempty, the dual of the grand-coalition shipping
LP (6) has an optimal solution, and for every optimal dual solution `(ν, γ, δ)` the allocation (8)
`α_n = ν_n H_n + ∑_w γ_w Y_{w,n} + δ_n E_n` lies in the core (7). -/
theorem dual_allocation_in_core {N W : ℕ} (sys : System N W) (Z : Profile N W) (hZ : Z.Nonneg)
    (D : Demand N) :
    (Core Finset.univ (fun S => coalitionValue sys S Z D)).Nonempty ∧
    (∃ p, IsOptimalDual sys Z D p) ∧
    ∀ p, IsOptimalDual sys Z D p →
      dualAllocation Z D p ∈ Core Finset.univ (fun S => coalitionValue sys S Z D) := by sorry

end DecentralizedDistribution.FirstBest
