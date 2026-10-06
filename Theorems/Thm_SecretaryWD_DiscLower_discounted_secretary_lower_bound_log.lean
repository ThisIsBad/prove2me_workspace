import Mathlib
import Definitions.Def_SecretaryWD_DiscLower_DiscountedSecretary
import Definitions.Def_SecretaryWD_DiscLower_HardInstances

namespace SecretaryWD.DiscLower

theorem discounted_secretary_lower_bound_log (c : ℕ) (hc : 2 ≤ c)
    (A : StoppingRule (horizon c)) :
    ∃ t : ℕ, 1 ≤ t ∧ t ≤ 2 * c ∧
      1 / 40 * (Real.log (horizon c) / Real.log (Real.log (horizon c))) *
          expectedValue (discount c) (hardInstance c t) A <
        expectedOPT (discount c) (hardInstance c t) := by sorry

end SecretaryWD.DiscLower

