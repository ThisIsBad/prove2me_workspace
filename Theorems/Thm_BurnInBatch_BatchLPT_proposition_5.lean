import Mathlib
import Definitions.Def_NumStochOpt_ListScheduling_ListSchedule
import Definitions.Def_NumStochOpt_ListScheduling_Makespan
import Definitions.Def_BurnInBatch_BatchLPT_Model
import Definitions.Def_BurnInBatch_BatchLPT_BLPT

namespace BurnInBatch.BatchLPT

open NumStochOpt.ListScheduling

theorem proposition_5 {n m B : ℕ} (hn : 0 < n) (hm : 0 < m) (hB : 0 < B)
    (p d : Fin n → ℝ) (hp : ∀ j, 0 < p j) (hd : ∀ j, 0 ≤ d j)
    (l : List (Fin n)) (hl : IsLPTList p l)
    (bl : List (Finset (Fin n))) (hbl : IsBLPTOrder p B l bl) :
    (blptLmax m p d bl - optLmax n m B p d) / (optLmax n m B p d + dMax d) ≤
      (1 / 3 - 1 / (3 * (m : ℝ))) + dMax d / (optLmax n m B p d + dMax d) := by sorry

end BurnInBatch.BatchLPT

