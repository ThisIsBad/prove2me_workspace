import Mathlib
import Definitions.Def_KellyStochasticNetworks_LossNetwork
import Definitions.Def_KellyStochasticNetworks_Balance

namespace KellyStochasticNetworks

theorem truncated_reversible {S : Type*} (π : S → ℝ) (q : S → S → ℝ) (A : Set S)
    (h : DetailedBalance π q) (Z : ℝ) (hZ0 : Z ≠ 0)
    (hZ : HasSum (fun j : A => π (j : S)) Z) :
    DetailedBalance (fun j : A => π (j : S) / Z) (truncatedRates q A)
      ∧ HasSum (fun j : A => π (j : S) / Z) 1 := by sorry

end KellyStochasticNetworks