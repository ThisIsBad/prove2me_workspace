import Mathlib
import Definitions.Def_ProcessingNetworks_BackPressure_SPNPlanningData
import Definitions.Def_ProcessingNetworks_BackPressure_LeontiefNetwork
import Definitions.Def_ProcessingNetworks_BackPressure_AllocationPolytope

namespace ProcessingNetworks.BackPressure

/-- Lemma 9.10, Dai & Harrison p. 174 (PDF p. 190): consider an SPN whose data satisfy
Assumption 9.1. For any `z ∈ ℝ^I_+` there is a `z`-maximal extreme allocation `β(z) ∈ E` with
`β_j(z) = 0` for every activity `j` whose served buffer is empty (`z_{i(j)} = 0`). -/
theorem z_maximal_extreme_idles_empty
    {I J K : ℕ} (dat : SPNPlanningData I J K) (h91 : SatisfiesAssumption91 dat)
    (z : Fin I → ℝ) (hz : ∀ i, 0 ≤ z i) :
    ∃ β ∈ ExtremeAllocations dat, IsZMaximal dat β z ∧
      ∀ j : Fin J, z (servesBuffer h91 j) = 0 → β j = 0 := by sorry

end ProcessingNetworks.BackPressure
