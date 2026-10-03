import Mathlib
import Definitions.Def_MDPFinance_OptimalStopping_Applications

open Filter Topology

namespace MDPFinance.OptimalStopping

/-- **Theorem 10.3.3** (p. 323). The optimal rule: reject the first `k^*` candidates, then take
the first leader — the stopping sets `{V_n = g}` are `{x > k^*}` on the states; the probability of
choosing the best candidate is `V_0(1) = (k^*/N) h(k^*)`; and `k^*(N)/N → 1/e`. -/
theorem theorem_10_3_3 (S : Secretary) :
    (∀ n : ℕ, n ≤ S.kStar →
      {x : ℕ | x ∈ Finset.Icc 1 S.N ∧ S.V n x = S.g x} =
        {x : ℕ | x ∈ Finset.Icc 1 S.N ∧ S.kStar < x}) ∧
    S.V 0 1 = ((S.kStar : ℝ) / (S.N : ℝ)) * S.h S.kStar ∧
    Tendsto (fun N : ℕ => (secretaryKStar N : ℝ) / (N : ℝ)) atTop (𝓝 (1 / Real.exp 1)) := by sorry

end MDPFinance.OptimalStopping
