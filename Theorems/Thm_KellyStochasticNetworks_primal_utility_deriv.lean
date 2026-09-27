import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_KellyStochasticNetworks_Congestion

namespace KellyStochasticNetworks

theorem primal_utility_deriv {J R : ℕ} (A : Fin J → Fin R → ℝ) (w : Fin R → ℝ)
    (p : Fin J → ℝ → ℝ) (hA : ∀ j r, A j r = 0 ∨ A j r = 1)
    (hp : ∀ j, Continuous (p j)) (x : Fin R → ℝ) (hx : ∀ r, 0 < x r) (r : Fin R) :
    HasDerivAt (fun t : ℝ => primalUtility A w p (Function.update x r t))
      (w r / x r - ∑ j, A j r * p j (linkFlow A x j)) (x r) := by sorry

end KellyStochasticNetworks
