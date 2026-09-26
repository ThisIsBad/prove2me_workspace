import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop

namespace KellyStochasticNetworks

theorem wardrop_from_minimizer {J R Sd : ℕ} (A : Fin J → Fin R → ℝ) (s : Fin R → Fin Sd)
    (D : Fin J → ℝ → ℝ) (f : Fin Sd → ℝ)
    (hA : ∀ j r, A j r = 0 ∨ A j r = 1)
    (hD : ∀ j, Continuous (D j)) (hmono : ∀ j, Monotone (D j))
    (x : Fin R → ℝ) (hx : x ∈ wardropFeasible s f)
    (hmin : ∀ z ∈ wardropFeasible s f, wardropObjective A D x ≤ wardropObjective A D z) :
    IsWardropEquilibrium A s D f x := by sorry

end KellyStochasticNetworks
