import Mathlib
import Definitions.Def_SecretaryWD_DiscLower_DiscountedSecretary
import Definitions.Def_SecretaryWD_DiscLower_HardInstances

namespace SecretaryWD.DiscLower

theorem competitive_stopByProb_ge (c : ℕ) (hc : 1 ≤ c) (A : StoppingRule (horizon c))
    (hA : ∀ s : ℕ, 1 ≤ s → s ≤ 2 * c →
      expectedOPT (discount c) (hardInstance c s) ≤
        (c : ℝ) / 10 * expectedValue (discount c) (hardInstance c s) A)
    (t : ℕ) (ht1 : 1 ≤ t) (ht2 : t ≤ 2 * c) :
    (t : ℝ) / c ≤ stopByProb (hardInstance c t) A (blockEnd c t) := by sorry

end SecretaryWD.DiscLower

