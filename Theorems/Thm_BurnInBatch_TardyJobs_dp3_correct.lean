import Mathlib
import Definitions.Def_BurnInBatch_TardyJobs_Model
import Definitions.Def_BurnInBatch_TardyJobs_DP3

namespace BurnInBatch.TardyJobs

/-- Correctness of Algorithm DP3, pp. 770–771, with zero included among
feasible on-time job counts when taking the maximum. -/
theorem dp3_correct {n : ℕ} (B p : ℕ) (r d : Fin n → ℕ)
    (hB : 0 < B) (hd : Monotone d) (hr : Monotone r) :
    n - dp3MaxOnTime B p r d = minTardy B (equalTime p) r d := by sorry

end BurnInBatch.TardyJobs

