import Mathlib
import Definitions.Def_SetCoverThreshold_SetCover_PartitionSystem

namespace SetCoverThreshold.SetCover

theorem lemma_3_2 (c : ℝ) (hc : 0 ≤ c) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ L k : ℕ,
      (L : ℝ) ≤ (Real.logb 2 m) ^ c → 2 ≤ k →
        (k : ℝ) < Real.log m / (3 * Real.log (Real.log m)) →
          Nonempty (PartitionSystem m L k ⌈(1 - 2 / (k : ℝ)) * k * Real.log m⌉₊) := by sorry

end SetCoverThreshold.SetCover
