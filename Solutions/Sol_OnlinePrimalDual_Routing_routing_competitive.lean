import Mathlib

namespace OnlinePrimalDual.Routing

end OnlinePrimalDual.Routing

open OnlinePrimalDual.Routing

theorem solution {J : Type*} [Fintype J]
    (Mcopy accepted : J → ℝ) (M loadPerCopy globalLoad n : ℝ)
    (hper_copy_bandwidth : ∀ j, Mcopy j ≤ accepted j)
    (hquota : M ≤ ∑ j, Mcopy j)
    (hn_pos : 0 < n)
    (hper_copy_load : loadPerCopy ≤ 2 + 6 * Real.logb 2 n)
    (hload_aggregation : globalLoad ≤ 4 * loadPerCopy) :
    M ≤ ∑ j, accepted j ∧ globalLoad ≤ 8 + 24 * Real.logb 2 n := by
  refine ⟨le_trans hquota (Finset.sum_le_sum fun j _ => hper_copy_bandwidth j), ?_⟩
  linarith
