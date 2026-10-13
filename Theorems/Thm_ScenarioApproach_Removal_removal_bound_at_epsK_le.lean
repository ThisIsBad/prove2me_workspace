import Mathlib
import Definitions.Def_ScenarioApproach_Removal_epsK

namespace ScenarioApproach.Removal

theorem removal_bound_at_epsK_le (N k d : ℕ) (hk : 1 ≤ k) (hd : 1 ≤ d) (hN : 1 ≤ N)
    (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hε1 : epsK N k d β ≤ 1) :
    ((k + d - 1).choose k : ℝ) * ∑ i ∈ Finset.range (k + d),
      (N.choose i : ℝ) * epsK N k d β ^ i * (1 - epsK N k d β) ^ (N - i) ≤ β := by sorry

end ScenarioApproach.Removal

