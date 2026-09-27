import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_KellyStochasticNetworks_Congestion

namespace KellyStochasticNetworks

theorem primal_lyapunov_deriv {J R : ℕ} (A : Fin J → Fin R → ℝ) (w κ : Fin R → ℝ)
    (p : Fin J → ℝ → ℝ) (hA : ∀ j r, A j r = 0 ∨ A j r = 1) (hκ : ∀ r, 0 < κ r)
    (hp : ∀ j, Continuous (p j))
    (x : ℝ → Fin R → ℝ) (t : ℝ) (hpos : ∀ r, 0 < x t r)
    (hode : ∀ r, HasDerivAt (fun s => x s r) (primalDrift A w κ p (x t) r) t) :
    HasDerivAt (fun s => primalUtility A w p (x s))
        (∑ r, (κ r / x t r)
          * (w r - x t r * ∑ j, A j r * p j (linkFlow A (x t) j)) ^ 2) t
      ∧ 0 ≤ ∑ r, (κ r / x t r)
          * (w r - x t r * ∑ j, A j r * p j (linkFlow A (x t) j)) ^ 2 := by sorry

end KellyStochasticNetworks
