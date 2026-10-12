import Mathlib
import Definitions.Def_WagelmansELS_Efficient_ThresholdRule

namespace WagelmansELS.Efficient

/-- Section 2, pp. S147, S149: consecutive slopes of the polygonal lower envelope
are strictly ordered at its breakpoints. -/
theorem ordered_ratios (P : Instance) (i t t' : ℕ)
    (hi : 1 ≤ i) (hin : i ≤ P.n)
    (ht : t ∈ P.E i) (ht' : t' ∈ P.E i)
    (hs : t' = P.succ i t) (hnext : t' < P.n + 1) :
    P.ratio i t > P.ratio i t' := by sorry

end WagelmansELS.Efficient

