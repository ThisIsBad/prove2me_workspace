import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_KellyStochasticNetworks_Congestion

namespace KellyStochasticNetworks

theorem primal_utility_strictConcave {J R : ℕ} (A : Fin J → Fin R → ℝ) (w : Fin R → ℝ)
    (p : Fin J → ℝ → ℝ) (hA : ∀ j r, 0 ≤ A j r) (hw : ∀ r, 0 < w r)
    (hp : ∀ j, Continuous (p j)) (hpmono : ∀ j, Monotone (p j)) (hpnn : ∀ j y, 0 ≤ p j y) :
    StrictConcaveOn ℝ {x : Fin R → ℝ | ∀ r, 0 < x r} (primalUtility A w p) := by sorry

end KellyStochasticNetworks
