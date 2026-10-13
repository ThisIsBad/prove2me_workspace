import Mathlib
import Definitions.Def_NumStochOpt_ListScheduling_ListSchedule
import Definitions.Def_NumStochOpt_ListScheduling_Makespan
import Definitions.Def_BurnInBatch_BatchLPT_Model
import Definitions.Def_BurnInBatch_BatchLPT_BLPT

namespace BurnInBatch.BatchLPT

open NumStochOpt.ListScheduling

theorem proposition_3 {n m B : ℕ} (hm : 0 < m) (hB : 0 < B) (p : Fin n → ℝ)
    (hp : ∀ j, 0 < p j) (l : List (Fin n)) (hl : IsLPTList p l)
    (bl : List (Finset (Fin n))) (hbl : IsBLPTOrder p B l bl) :
    blptMakespan m p bl ≤ (4 / 3 - 1 / (3 * (m : ℝ))) * optBatchMakespan n m B p := by sorry

end BurnInBatch.BatchLPT

