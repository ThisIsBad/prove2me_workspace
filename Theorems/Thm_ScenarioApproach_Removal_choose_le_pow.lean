import Mathlib

namespace ScenarioApproach.Removal

theorem choose_le_pow (k d : ℕ) (hd : 1 ≤ d) :
    ((k + d - 1).choose k : ℝ) =
        ((k + d - 1).factorial : ℝ) / ((k.factorial : ℝ) * ((d - 1).factorial : ℝ)) ∧
      (k + d - 1).choose k ≤ (k + d - 1) ^ (d - 1) := by sorry

end ScenarioApproach.Removal

