import Mathlib

namespace BurnInBatch.AgreeTmax

/-- Algorithm FBEDD (Full-Batch EDD) of Lee, Uzsoy & Martin-Vega (1992), p. 769: group the `B`
jobs with the smallest indices into a batch, the next `B` into the next, and so on (the last batch
may hold fewer than `B` jobs), and process the batches in this order. Batch `k` (0-based) is the
set of jobs with 0-based index in `[k B, (k + 1) B)`; there are `⌈n / B⌉` batches. -/
def fbedd (n B : ℕ) : List (Finset (Fin n)) :=
  (List.range ((n + B - 1) / B)).map fun k =>
    Finset.univ.filter fun i : Fin n => k * B ≤ i.val ∧ i.val < (k + 1) * B

end BurnInBatch.AgreeTmax
