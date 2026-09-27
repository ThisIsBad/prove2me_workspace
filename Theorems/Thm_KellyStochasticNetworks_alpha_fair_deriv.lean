import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_KellyStochasticNetworks_Congestion
import Definitions.Def_KellyStochasticNetworks_FlowLevel

namespace KellyStochasticNetworks

theorem alpha_fair_deriv {R : ℕ} (w n : Fin R → ℝ) (α : ℝ) (hα : 0 < α)
    (hw : ∀ r, 0 < w r) (hn : ∀ r, 0 < n r) (X : Fin R → ℝ) (hX : ∀ r, 0 < X r) (r : Fin R) :
    HasDerivAt (fun t : ℝ => alphaFairObjective w n α (Function.update X r t))
      (w r * n r ^ α * X r ^ (-α)) (X r) := by sorry

end KellyStochasticNetworks
