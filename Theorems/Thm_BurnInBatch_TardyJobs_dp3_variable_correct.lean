import Mathlib
import Definitions.Def_BurnInBatch_TardyJobs_Model
import Definitions.Def_BurnInBatch_TardyJobs_DP3Variable

namespace BurnInBatch.TardyJobs

/-- The §4 extension of DP3, p. 771, to agreeable processing times and due dates. -/
theorem dp3_variable_correct {n : ℕ} (B : ℕ) (p d : Fin n → ℕ)
    (hB : 0 < B) (hd : Monotone d) (hp : Monotone p) :
    n - dp3VariableMaxOnTime B p d = minTardy B p (fun _ => 0) d := by sorry

end BurnInBatch.TardyJobs

