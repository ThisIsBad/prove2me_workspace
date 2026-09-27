import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_KellyStochasticNetworks_Congestion
import Definitions.Def_KellyStochasticNetworks_FlowLevel

namespace KellyStochasticNetworks

theorem alpha_fair_drift_negative {J R : ℕ} (A : Fin J → Fin R → ℝ) (C : Fin J → ℝ)
    (w ρ : Fin R → ℝ) (α : ℝ) (hα : 0 < α)
    (hA : ∀ j r, A j r = 0 ∨ A j r = 1) (hw : ∀ r, 0 < w r) (hρ : ∀ r, 0 < ρ r)
    (hstab : ∀ j, linkFlow A ρ j < C j) :
    ∃ ε > 0, ∀ n : Fin R → ℝ, (∀ r, 0 < n r) →
      ∀ X : Fin R → ℝ, (∀ r, 0 < X r) → X ∈ networkFeasible A C →
        IsMaxOn (alphaFairObjective w n α) (networkFeasible A C ∩ {Y | ∀ r, 0 < Y r}) X →
        (∑ r, w r * ρ r ^ (-α) * n r ^ α * (ρ r - X r))
          ≤ -ε * ∑ r, w r * n r ^ α * ρ r ^ (1 - α) := by sorry

end KellyStochasticNetworks
