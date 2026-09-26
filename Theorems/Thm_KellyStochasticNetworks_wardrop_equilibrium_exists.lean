import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop

namespace KellyStochasticNetworks

theorem wardrop_equilibrium_exists {J R Sd : ℕ} (A : Fin J → Fin R → ℝ) (s : Fin R → Fin Sd)
    (D : Fin J → ℝ → ℝ) (f : Fin Sd → ℝ)
    (hA : ∀ j r, A j r = 0 ∨ A j r = 1)
    (hD : ∀ j, Continuous (D j)) (hmono : ∀ j, Monotone (D j))
    (hf : ∀ σ, 0 ≤ f σ) (hserved : ∀ σ, ∃ r, s r = σ) :
    ∃ x : Fin R → ℝ, IsWardropEquilibrium A s D f x := by sorry

end KellyStochasticNetworks
