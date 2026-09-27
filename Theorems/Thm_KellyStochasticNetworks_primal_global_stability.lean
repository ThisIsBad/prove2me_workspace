import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_KellyStochasticNetworks_Congestion

namespace KellyStochasticNetworks

theorem primal_global_stability {J R : ℕ} (A : Fin J → Fin R → ℝ) (w κ : Fin R → ℝ)
    (p : Fin J → ℝ → ℝ) (hA : ∀ j r, A j r = 0 ∨ A j r = 1)
    (hw : ∀ r, 0 < w r) (hκ : ∀ r, 0 < κ r)
    (hp : ∀ j, Continuous (p j)) (hpmono : ∀ j, Monotone (p j))
    (hpnn : ∀ j y, 0 ≤ p j y) (hpne : ∀ j, ∃ y, p j y ≠ 0)
    (xbar : Fin R → ℝ) (hbarpos : ∀ r, 0 < xbar r)
    (hbar : ∀ r, w r = xbar r * ∑ j, A j r * p j (linkFlow A xbar j))
    (x : ℝ → Fin R → ℝ) (hxpos : ∀ t, 0 ≤ t → ∀ r, 0 < x t r)
    (hode : ∀ t, 0 ≤ t → ∀ r,
      HasDerivAt (fun s => x s r) (primalDrift A w κ p (x t) r) t) :
    IsMaxOn (primalUtility A w p) {y : Fin R → ℝ | ∀ r, 0 < y r} xbar
      ∧ Filter.Tendsto x Filter.atTop (nhds xbar) := by sorry

end KellyStochasticNetworks
