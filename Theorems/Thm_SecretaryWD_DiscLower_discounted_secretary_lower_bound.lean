import Mathlib
import Definitions.Def_SecretaryWD_DiscLower_DiscountedSecretary
import Definitions.Def_SecretaryWD_DiscLower_HardInstances

namespace SecretaryWD.DiscLower

theorem discounted_secretary_lower_bound (c : ℕ) (hc : 1 ≤ c) (A : StoppingRule (horizon c)) :
    ∃ t : ℕ, 1 ≤ t ∧ t ≤ 2 * c ∧
      (c : ℝ) * expectedValue (discount c) (hardInstance c t) A <
        10 * expectedOPT (discount c) (hardInstance c t) := by sorry

end SecretaryWD.DiscLower

