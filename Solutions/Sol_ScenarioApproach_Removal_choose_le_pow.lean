import Mathlib



namespace ScenarioApproach.Removal

theorem choose_le_pow_core (k d : ℕ) (hd : 1 ≤ d) :
    ((k + d - 1).choose k : ℝ) =
        ((k + d - 1).factorial : ℝ) / ((k.factorial : ℝ) * ((d - 1).factorial : ℝ)) ∧
      (k + d - 1).choose k ≤ (k + d - 1) ^ (d - 1) := by
  have hk : k ≤ k + d - 1 := by omega
  have hsub : k + d - 1 - k = d - 1 := by omega
  constructor
  · rw [Nat.cast_choose ℝ hk, hsub]
  · rw [← Nat.choose_symm hk, hsub]
    exact Nat.choose_le_pow _ _

end ScenarioApproach.Removal

open ScenarioApproach.Removal


theorem solution (k d : ℕ) (hd : 1 ≤ d) :
    ((k + d - 1).choose k : ℝ) =
        ((k + d - 1).factorial : ℝ) / ((k.factorial : ℝ) * ((d - 1).factorial : ℝ)) ∧
      (k + d - 1).choose k ≤ (k + d - 1) ^ (d - 1) := by
  exact choose_le_pow_core k d hd
