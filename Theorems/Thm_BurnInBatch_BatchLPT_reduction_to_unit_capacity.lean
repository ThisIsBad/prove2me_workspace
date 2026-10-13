import Mathlib
import Definitions.Def_NumStochOpt_ListScheduling_ListSchedule
import Definitions.Def_NumStochOpt_ListScheduling_Makespan
import Definitions.Def_BurnInBatch_BatchLPT_Model
import Definitions.Def_BurnInBatch_BatchLPT_BLPT

namespace BurnInBatch.BatchLPT

open NumStochOpt.ListScheduling

theorem reduction_to_unit_capacity {n m B : ℕ} (hm : 0 < m) (hB : 0 < B) (p : Fin n → ℝ)
    (hp : ∀ j, 0 < p j) (l : List (Fin n)) (hl : IsLPTList p l) :
    optBatchMakespan n m B p =
      optMakespan (blptBatches B l).length m (BurnInBatch.ListSched.batchTimes p (blptBatches B l)) := by sorry

end BurnInBatch.BatchLPT

