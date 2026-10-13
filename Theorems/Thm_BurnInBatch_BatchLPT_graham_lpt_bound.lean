import Mathlib
import Definitions.Def_NumStochOpt_ListScheduling_ListSchedule
import Definitions.Def_NumStochOpt_ListScheduling_Makespan

namespace BurnInBatch.BatchLPT

open NumStochOpt.ListScheduling

theorem graham_lpt_bound {M m : ℕ} (hm : 0 < m) (q : ℕ → ℝ)
    (hq_nonneg : ∀ k, k < M → 0 ≤ q k)
    (hq_noninc : ∀ k k', k ≤ k' → k' < M → q k' ≤ q k) :
    listMakespan M m q ≤ (4 / 3 - 1 / (3 * (m : ℝ))) * optMakespan M m q := by sorry

end BurnInBatch.BatchLPT

