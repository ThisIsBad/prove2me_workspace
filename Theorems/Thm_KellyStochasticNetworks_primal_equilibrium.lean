import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_KellyStochasticNetworks_Congestion

namespace KellyStochasticNetworks

theorem primal_equilibrium {J R : ℕ} (A : Fin J → Fin R → ℝ) (w κ : Fin R → ℝ)
    (p : Fin J → ℝ → ℝ) (hκ : ∀ r, 0 < κ r) (x : Fin R → ℝ) (hx : ∀ r, 0 < x r) :
    (∀ r, w r / x r - ∑ j, A j r * p j (linkFlow A x j) = 0)
      ↔ ∀ r, primalDrift A w κ p x r = 0 := by sorry

end KellyStochasticNetworks
