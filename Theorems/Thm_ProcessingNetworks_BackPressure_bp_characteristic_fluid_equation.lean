import Mathlib
import Definitions.Def_ProcessingNetworks_BackPressure_SPNPlanningData
import Definitions.Def_ProcessingNetworks_BackPressure_LeontiefNetwork
import Definitions.Def_ProcessingNetworks_BackPressure_AllocationPolytope
import Definitions.Def_ProcessingNetworks_BackPressure_RegularPoint
import Definitions.Def_ProcessingNetworks_BackPressure_FluidModelSolution

namespace ProcessingNetworks.BackPressure

open Filter

/-- Theorem 9.8, Dai & Harrison p. 173 (PDF p. 189): consider an SPN satisfying Assumption 9.1
and operating under the relaxed back-pressure control policy. Each fluid limit path
`(D̂,F̂,T̂,Ẑ)` satisfies `R Ṫ(t)·Ẑ(t) = max_{β∈A} p(β,Ẑ(t))` (9.22) at each regular point —
i.e. `Ṫ(t)` is itself a `Ẑ(t)`-maximal allocation. The hypothesis that the fluid limit path
"operates under relaxed back-pressure control" is formalized via Lemma 9.11's conclusion
(9.28)-(9.31), an extreme-allocation decomposition `Ŷ` of `T̂` over the set `E` of extreme allocations,
exactly as the book's own proof of this theorem invokes Lemma 9.11 directly; the regular point is
regular for the fluid limit path `(D̂, F̂, T̂, Ẑ, Ŷ)` of Lemma 9.11, `Ŷ` included, as the proof's
"`∑_β Ẏ_β(t) = 1`" requires. -/
theorem bp_characteristic_fluid_equation
    {I J K : ℕ} (dat : SPNPlanningData I J K) (h91 : SatisfiesAssumption91 dat) (lam : Fin I → ℝ)
    (E : Finset (Fin J → ℝ)) (hE : (E : Set (Fin J → ℝ)) = ExtremeAllocations dat)
    (Dh : ℝ → Fin I → ℝ) (Fh Th : ℝ → Fin J → ℝ) (Zh : ℝ → Fin I → ℝ)
    (hsol : IsFluidModelSolution dat lam Dh Fh Th Zh)
    (Yh : (Fin J → ℝ) → ℝ → ℝ)
    (hTY : ∀ t : ℝ, 0 ≤ t → ∀ j, Th t j = ∑ β ∈ E, β j * Yh β t)
    (hYmono : ∀ β ∈ E, Monotone (Yh β))
    (hYsum : ∀ t : ℝ, 0 ≤ t → ∑ β ∈ E, Yh β t = t)
    (hYopt : ∀ β ∈ E, ∀ t : ℝ, 0 < t → p dat β (Zh t) < ⨆ α ∈ E, p dat α (Zh t) →
      ∀ d : ℝ, HasDerivAt (Yh β) d t → d = 0)
    (t : ℝ) (ht : 0 < t) (hreg : RegularPoint Dh Fh Th Zh t)
    (hYreg : ∀ β ∈ E, DifferentiableAt ℝ (Yh β) t) :
    ∀ d : Fin J → ℝ, HasDerivAt Th d t → IsZMaximal dat d (Zh t) := by sorry

end ProcessingNetworks.BackPressure
