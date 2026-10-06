import Mathlib
import Definitions.Def_SecretaryWD_DiscUpper_Algorithm

namespace SecretaryWD.DiscUpper
theorem class_payoff_lower_bound (n : ℕ) (d v : Fin n → ℝ)
    (hd : ∀ t, 0 ≤ d t) (hv : ∀ e, 0 ≤ v e) (c : ℕ) (hc : 1 ≤ c) :
    optClass d v c / (2 * Real.exp 1) ≤ classValue d v c := by sorry
end SecretaryWD.DiscUpper

