import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance

namespace KellyStochasticNetworks

theorem reversed_process_rates {S : Type*} [Fintype S] (π : S → ℝ) (q : S → S → ℝ)
    (hπ : ∀ j, 0 < π j) (h : FullBalance π q) :
    (∀ j : S, (∑' k : S, reversedRates π q j k) = ∑' k : S, q j k) ∧
      FullBalance π (reversedRates π q) := by sorry

end KellyStochasticNetworks
