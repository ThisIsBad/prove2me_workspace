import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance

namespace KellyStochasticNetworks

theorem reversible_iff_detailed_balance {S : Type*} (π : S → ℝ) (q : S → S → ℝ)
    (hπ : ∀ j, 0 < π j) : reversedRates π q = q ↔ DetailedBalance π q := by sorry

end KellyStochasticNetworks
