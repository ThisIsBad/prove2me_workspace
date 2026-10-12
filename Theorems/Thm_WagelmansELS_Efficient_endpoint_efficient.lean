import Mathlib
import Definitions.Def_WagelmansELS_Efficient_EfficientPeriods

namespace WagelmansELS.Efficient

/-- Section 2, p. S147: the right endpoint of the envelope is `(D(i+1),G(i+1))`;
p. S148 declares the left endpoint `(0,0)` a breakpoint. -/
theorem endpoint_efficient (P : Instance) (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ P.n) :
    (∀ t ∈ Finset.Ioc i (P.n + 1), i + 1 < t → P.D t = P.D (i + 1) →
      P.G (i + 1) ≤ P.G t) ∧
    P.IsEfficient i (i + 1) ∧ P.IsEfficient i (P.n + 1) := by sorry

end WagelmansELS.Efficient

