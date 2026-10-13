import Mathlib

namespace ScenarioApproach.Removal

theorem binomial_sum_le_exp (N k d : ℕ) (hk : 1 ≤ k) (hd : 1 ≤ d)
    (a : ℝ) (ha : a = 1 + 1 / Real.sqrt k)
    (εk : ℝ) (hε0 : 0 ≤ εk) (hε1 : εk ≤ 1) :
    (∑ i ∈ Finset.range (k + d), (N.choose i : ℝ) * εk ^ i * (1 - εk) ^ (N - i) ≤
        a ^ (k + d - 1) * (1 - (1 - 1 / a) * εk) ^ N) ∧
      (∑ i ∈ Finset.range (k + d), (N.choose i : ℝ) * εk ^ i * (1 - εk) ^ (N - i) ≤
        Real.exp (-(1 - a) * ((k + d - 1 : ℕ) : ℝ)) * Real.exp (-(1 - 1 / a) * εk * N)) := by sorry

end ScenarioApproach.Removal

