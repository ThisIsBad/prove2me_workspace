import Mathlib
import Definitions.Def_NonmonotoneLS_Shared_Params
import Definitions.Def_NonmonotoneLS_Shared_Cost
import Definitions.Def_NonmonotoneLS_Shared_Steps
import Definitions.Def_NonmonotoneLS_Global_Run
import Definitions.Def_NonmonotoneLS_Global_Regions

open scoped InnerProductSpace NNReal Topology
open Filter

namespace NonmonotoneLS.Global

/-- Eq. (1.8) (p. 1045): if `η_k ∈ [0, 1]` for all `k`, then
`Q_{j+1} = 1 + ∑_{i=0}^{j} ∏_{m=0}^{i} η_{j-m} ≤ j + 2`. -/
theorem costQ_closed_form (η : ℕ → ℝ) (hη : ∀ k, η k ∈ Set.Icc (0 : ℝ) 1) (j : ℕ) :
    Shared.costQ η (j + 1) =
        1 + ∑ i ∈ Finset.range (j + 1), ∏ m ∈ Finset.range (i + 1), η (j - m) ∧
      Shared.costQ η (j + 1) ≤ (j : ℝ) + 2 := by sorry

end NonmonotoneLS.Global
