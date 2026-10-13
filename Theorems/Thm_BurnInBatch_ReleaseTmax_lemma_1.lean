import Mathlib
import Definitions.Def_BurnInBatch_ReleaseTmax_Model

namespace BurnInBatch.ReleaseTmax

/-- Lemma 1 (p. 767). One batch machine of capacity `B`, `n` jobs with common processing time
`p`, release times `r` and due dates `d` that are agreeable (`r_i < r_j → d_i ≤ d_j`). If some
batch schedule of all `n` jobs has every job on time (`T_max = 0`), then some batch schedule of
all `n` jobs has every job on time and is in batch-EDD order. -/
theorem lemma_1 {n : ℕ} (B p : ℕ) (r d : Fin n → ℕ)
    (hagree : ∀ i j : Fin n, r i < r j → d i ≤ d j)
    (hfeas : ∃ S : List (Finset (Fin n)),
      IsBatchSchedule B Finset.univ S ∧ AllOnTime p r d Finset.univ S) :
    ∃ S : List (Finset (Fin n)),
      IsBatchSchedule B Finset.univ S ∧ AllOnTime p r d Finset.univ S ∧ IsBatchEDD d S := by sorry

end BurnInBatch.ReleaseTmax

