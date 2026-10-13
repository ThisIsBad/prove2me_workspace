import Mathlib
import Definitions.Def_BurnInBatch_TardyJobs_Model

namespace BurnInBatch.TardyJobs

/-- Lemma 4, p. 770: an optimal schedule can put every on-time batch first,
with those batches in batch-EDD order, and all tardy jobs afterward. -/
theorem lemma_4 {n : ℕ} (B p : ℕ) (r d : Fin n → ℕ)
    (hB : 0 < B) (hagree : ∀ i j : Fin n, r i < r j → d i ≤ d j) :
    ∃ A T : List (Finset (Fin n)),
      Optimal B (equalTime p) r d (A ++ T) ∧
      (∀ P ∈ A, ∀ j ∈ P, jobCompletion (equalTime p) r (A ++ T) j ≤ d j) ∧
      (∀ P ∈ T, ∀ j ∈ P, d j < jobCompletion (equalTime p) r (A ++ T) j) ∧
      BatchEDD d A := by sorry

end BurnInBatch.TardyJobs

