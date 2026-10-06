import Mathlib
import Definitions.Def_SecretaryWD_DiscUpper_Algorithm

namespace SecretaryWD.DiscUpper
theorem discounted_secretary_upper_bound (n : ℕ) (hn : 1 ≤ n) (d v : Fin n → ℝ)
    (hd : ∀ t, 0 ≤ d t) (hv : ∀ e, 0 ≤ v e) :
    expectedOpt d v ≤ 4 * Real.exp 1 * (classCount n : ℝ) * algorithmValue d v := by sorry
end SecretaryWD.DiscUpper

