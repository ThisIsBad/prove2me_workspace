import Mathlib
import Definitions.Def_SecretaryWD_DiscLower_DiscountedSecretary
import Definitions.Def_SecretaryWD_DiscLower_HardInstances

namespace SecretaryWD.DiscLower

theorem stopByProb_coupling (c t : ℕ) (hc : 1 ≤ c) (ht1 : 1 ≤ t) (ht2 : t < 2 * c)
    (A : StoppingRule (horizon c)) :
    stopByProb (hardInstance c t) A (blockEnd c t) - 1 / (c : ℝ) ^ 2 ≤
      stopByProb (hardInstance c (t + 1)) A (blockEnd c t) := by sorry

end SecretaryWD.DiscLower

