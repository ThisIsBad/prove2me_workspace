import Mathlib
import Definitions.Def_SecretaryWD_DiscLower_DiscountedSecretary
import Definitions.Def_SecretaryWD_DiscLower_HardInstances

namespace SecretaryWD.DiscLower

theorem expectedOPT_hardInstance_ge (c t : ℕ) (hc : 1 ≤ c) (ht1 : 1 ≤ t) (ht2 : t ≤ 2 * c) :
    (1 - 1 / Real.exp 1) * (bigK c : ℝ) ^ t * ((c : ℝ) ^ t)⁻¹ ≤
      expectedOPT (discount c) (hardInstance c t) := by sorry

end SecretaryWD.DiscLower

