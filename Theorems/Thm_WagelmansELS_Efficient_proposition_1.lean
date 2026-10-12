import Mathlib
import Definitions.Def_WagelmansELS_Efficient_EfficientPeriods

namespace WagelmansELS.Efficient

/-- Proposition 1, p. S148: removing non-breakpoint periods leaves the minimum unchanged. -/
theorem proposition_1 (P : Instance) (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ P.n) :
    (P.E i).Nonempty ∧
    ∀ h : (P.E i).Nonempty,
      (Finset.Ioc i (P.n + 1)).inf' (by simp; omega) (P.score i) =
        (P.E i).inf' h (P.score i) := by sorry

end WagelmansELS.Efficient

