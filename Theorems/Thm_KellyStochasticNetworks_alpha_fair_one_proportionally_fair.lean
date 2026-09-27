import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_KellyStochasticNetworks_Congestion
import Definitions.Def_KellyStochasticNetworks_FlowLevel

namespace KellyStochasticNetworks

theorem alpha_fair_one_proportionally_fair {J R : ℕ} (A : Fin J → Fin R → ℝ) (C : Fin J → ℝ)
    (w n : Fin R → ℝ) (hA : ∀ j r, 0 ≤ A j r) (hw : ∀ r, 0 < w r) (hn : ∀ r, 0 < n r)
    (X : Fin R → ℝ) (hXpos : ∀ r, 0 < X r) (hXfeas : X ∈ networkFeasible A C) :
    IsMaxOn (alphaFairObjective w n 1) (networkFeasible A C ∩ {Y | ∀ r, 0 < Y r}) X
      ↔ ∀ Y ∈ networkFeasible A C, (∑ r, w r * n r * ((Y r - X r) / X r)) ≤ 0 := by sorry

end KellyStochasticNetworks
