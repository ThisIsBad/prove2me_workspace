import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_KellyStochasticNetworks_Congestion

namespace KellyStochasticNetworks

theorem proportional_fair_iff {J R : ℕ} (A : Fin J → Fin R → ℝ) (C : Fin J → ℝ)
    (w : Fin R → ℝ) (hA : ∀ j r, 0 ≤ A j r) (hw : ∀ r, 0 < w r)
    (x : Fin R → ℝ) (hxpos : ∀ r, 0 < x r) (hxfeas : x ∈ networkFeasible A C) :
    IsMaxOn (networkObjective w) (networkFeasible A C ∩ {y | ∀ r, 0 < y r}) x
      ↔ ∀ y ∈ networkFeasible A C, (∑ r, w r * ((y r - x r) / x r)) ≤ 0 := by sorry

end KellyStochasticNetworks
