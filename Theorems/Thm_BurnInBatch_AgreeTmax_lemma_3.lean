import Mathlib
import Definitions.Def_BurnInBatch_AgreeTmax_Model

namespace BurnInBatch.AgreeTmax

/-- Lemma 3 of Lee, Uzsoy & Martin-Vega (1992), p. 769: in `1/B/T_max` with agreeable processing
times and due dates (strict form `p i < p j → d i ≤ d j`), if some valid batch schedule of all `n`
jobs has `T_max = 0`, then some valid batch schedule with `T_max = 0` is in batch-EDD order. -/
theorem lemma_3 {n B : ℕ} (hB : 0 < B) (p d : Fin n → ℕ) (hagr : Agreeable p d)
    (hfeas : ∃ S : List (Finset (Fin n)), IsValid B Finset.univ S ∧ Tmax p d S = 0) :
    ∃ S : List (Finset (Fin n)), IsValid B Finset.univ S ∧ Tmax p d S = 0 ∧ IsBatchEDD d S := by sorry

end BurnInBatch.AgreeTmax

