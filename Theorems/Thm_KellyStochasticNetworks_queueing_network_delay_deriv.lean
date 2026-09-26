import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop

namespace KellyStochasticNetworks

theorem queueing_network_delay_deriv {J R : ℕ} (A : Fin J → Fin R → ℝ) (w ν : Fin R → ℝ)
    (φ : Fin J → ℝ) (hA : ∀ j r, A j r = 0 ∨ A j r = 1)
    (hstab : ∀ j, (∑ r', A j r' * ν r') < φ j) (r : Fin R) :
    HasDerivAt (fun t : ℝ => queueingCost A w (Function.update ν r t) φ)
      (∑ j, A j r * (w r / (φ j - ∑ r', A j r' * ν r')
        + ∑ r', A j r' * (ν r' * w r') / (φ j - ∑ r'', A j r'' * ν r'') ^ 2))
      (ν r) := by sorry

end KellyStochasticNetworks
