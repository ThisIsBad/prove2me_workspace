import Mathlib
import Definitions.Def_MDPFinance_OptimalStopping_Applications

namespace MDPFinance.OptimalStopping

/-- **Proposition 10.3.2** (p. 322). For `n = 0,…,N-1` and states `x ∈ {1,…,N}`:
`V_n(x) = 1` if `x = N`; `= x/N` if `x = k^*+1,…,N-1`; `= (k^*/N) h(k^*)` if `x = n,…,k^*`
(with `x ≥ 1`, the states of the chain). -/
theorem proposition_10_3_2 (S : Secretary) (n : ℕ) (hn : n < S.N) :
    (S.V n S.N = 1) ∧
    (∀ x : ℕ, S.kStar + 1 ≤ x → x ≤ S.N - 1 → S.V n x = (x : ℝ) / (S.N : ℝ)) ∧
    (∀ x : ℕ, 1 ≤ x → n ≤ x → x ≤ S.kStar →
      S.V n x = ((S.kStar : ℝ) / (S.N : ℝ)) * S.h S.kStar) := by sorry

end MDPFinance.OptimalStopping
