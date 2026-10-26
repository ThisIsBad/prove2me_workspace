import Mathlib
import Definitions.Def_CHMSPricing_SpmPartition_ValueDist
import Definitions.Def_CHMSPricing_SpmPartition_SetSystem
import Definitions.Def_CHMSPricing_SpmPartition_Mechanism

namespace CHMSPricing.SpmPartition

theorem sum_servProb_le_rank {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : ι → ValueDist) (J : SetSystem ι) (M : Mechanism ι) (hM : IsTruthful D J M)
    (S : Finset ι) :
    ∑ i ∈ S, servProb D M i ≤ (J.rank S : ℝ) := by sorry

end CHMSPricing.SpmPartition

