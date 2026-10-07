import Mathlib

namespace WeightedMajority.Shattered

/-- Littlestone--Warmuth, Lemma 7.2, p. 244. `r i = 2 ^ k i` encodes
the assertion that `log₂ (r i)` is an integer. -/
theorem lemma_7_2 {j : ℕ} (r : Fin j → ℝ) (k : Fin j → ℤ)
    (hr : ∀ i, r i = (2 : ℝ) ^ (k i)) (l : ℤ)
    (hmax : ∀ i, r i ≤ (2 : ℝ) ^ l)
    (hsum : (2 : ℝ) ^ l ≤ ∑ i, r i) :
    ∃ K : Finset (Fin j), ∑ i ∈ K, r i = (2 : ℝ) ^ l := by sorry

end WeightedMajority.Shattered

