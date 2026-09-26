import Mathlib
import Definitions.Def_KellyStochasticNetworks_LossNetwork
import Definitions.Def_KellyStochasticNetworks_Balance

namespace KellyStochasticNetworks

theorem dual_optimum_conditions {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν : Fin R → ℝ)
    (C : Fin J → ℕ) (hν : ∀ r, 0 < ν r) (y : Fin J → ℝ) (hy : ∀ j, 0 ≤ y j)
    (hmin : ∀ z : Fin J → ℝ, (∀ j, 0 ≤ z j) → dualObjective A ν C y ≤ dualObjective A ν C z) :
    ∀ j, (0 < y j →
            (∑ r, (A j r : ℝ) * ν r * Real.exp (-∑ i, y i * (A i r : ℝ))) = (C j : ℝ))
      ∧ (y j = 0 →
            (∑ r, (A j r : ℝ) * ν r * Real.exp (-∑ i, y i * (A i r : ℝ))) ≤ (C j : ℝ)) := by sorry

end KellyStochasticNetworks