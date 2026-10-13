import Mathlib
import Definitions.Def_NumStochOpt_ListScheduling_ListSchedule
import Definitions.Def_NumStochOpt_ListScheduling_Makespan
import Definitions.Def_BurnInBatch_BatchLPT_Model
import Definitions.Def_BurnInBatch_BatchLPT_BLPT

namespace BurnInBatch.BatchLPT

open NumStochOpt.ListScheduling

theorem proposition_2 {n m B : ℕ} (hm : 0 < m) (hB : 0 < B) (p : Fin n → ℝ)
    (hp : ∀ j, 0 < p j) (l : List (Fin n)) (hl : IsLPTList p l) :
    ∃ S : List (Finset (Fin n)), ∃ σ : Fin S.length → Fin m,
      IsBatching n B S ∧ S.Perm (blptBatches B l) ∧
      makespan (BurnInBatch.ListSched.batchTimes p S) σ = optBatchMakespan n m B p := by sorry

end BurnInBatch.BatchLPT

