import Mathlib
import Definitions.Def_WagelmansELS_Efficient_ThresholdRule

namespace WagelmansELS.Efficient

/-- Proposition 2, p. S149: the ratio decides which of two consecutive efficient
periods has the lower candidate cost. -/
theorem proposition_2 (P : Instance) (i k : ℕ)
    (hi : 1 ≤ i) (hin : i ≤ P.n)
    (hk : k ∈ P.E i) (hnext : k < P.n + 1) :
    (P.ratio i k < P.c i → P.score i k < P.score i (P.succ i k)) ∧
    (¬ P.ratio i k < P.c i → P.score i (P.succ i k) ≤ P.score i k) := by sorry

end WagelmansELS.Efficient

