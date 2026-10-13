import Mathlib
import Definitions.Def_BurnInBatch_TardyJobs_Model

namespace BurnInBatch.TardyJobs

/-- Lemma 5, p. 770: in an optimum, every entirely on-time batch
consists of consecutive job indices. -/
theorem lemma_5 {n : ℕ} (B p : ℕ) (r d : Fin n → ℕ)
    (hB : 0 < B) (hd : Monotone d) (hr : Monotone r) :
    ∃ S : List (Finset (Fin n)),
      Optimal B (equalTime p) r d S ∧
      ∀ P ∈ S,
        (∀ j ∈ P, jobCompletion (equalTime p) r S j ≤ d j) → Consecutive P := by sorry

end BurnInBatch.TardyJobs

