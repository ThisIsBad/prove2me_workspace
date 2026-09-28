import Mathlib
import Definitions.Def_NonmonotoneLS_Shared_Params
import Definitions.Def_NonmonotoneLS_Shared_Cost
import Definitions.Def_NonmonotoneLS_Shared_Steps
import Definitions.Def_NonmonotoneLS_Global_Run
import Definitions.Def_NonmonotoneLS_Global_Regions

open scoped InnerProductSpace NNReal Topology
open Filter

namespace NonmonotoneLS.Global

/-- Eq. (2.15) (p. 1048): if `η_k ∈ [0, η_max]` for all `k` and `η_max < 1`, then
`Q_{k+1} ≤ 1 + ∑_{j=0}^{k} η_max^{j+1} ≤ 1/(1 - η_max)`. -/
theorem costQ_le_inv (η : ℕ → ℝ) (ηmax : ℝ) (hη : ∀ k, η k ∈ Set.Icc (0 : ℝ) ηmax)
    (hηmax : ηmax < 1) (k : ℕ) :
    Shared.costQ η (k + 1) ≤ 1 + ∑ j ∈ Finset.range (k + 1), ηmax ^ (j + 1) ∧
      1 + ∑ j ∈ Finset.range (k + 1), ηmax ^ (j + 1) ≤ 1 / (1 - ηmax) := by sorry

end NonmonotoneLS.Global
