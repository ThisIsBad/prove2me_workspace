import Mathlib
import Definitions.Def_BurnInBatch_ReleaseTmax_Model

namespace BurnInBatch.ReleaseTmax

/-- Lemma 2 (p. 769), with the assumption `r_j + p ≤ d_j` of its proof. One batch machine of
capacity `B ≥ 1`, `n` jobs with common processing time `p`, agreeable release times and due
dates, and `r_j + p ≤ d_j` for every job. Then some batch schedule of all `n` jobs has maximum
tardiness at most `(n − 1)p`. -/
theorem lemma_2 {n : ℕ} (B p : ℕ) (r d : Fin n → ℕ) (hB : 0 < B)
    (hagree : ∀ i j : Fin n, r i < r j → d i ≤ d j)
    (hrd : ∀ j : Fin n, r j + p ≤ d j) :
    ∃ S : List (Finset (Fin n)),
      IsBatchSchedule B Finset.univ S ∧ tmax p r d Finset.univ S ≤ (n - 1) * p := by sorry

end BurnInBatch.ReleaseTmax

