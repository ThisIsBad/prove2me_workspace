import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_KellyStochasticNetworks_Congestion
import Definitions.Def_KellyStochasticNetworks_FlowLevel

namespace KellyStochasticNetworks

theorem alpha_fair_drift_identity {R : ℕ} (w n ν μ x : Fin R → ℝ) (α : ℝ)
    (hμ : ∀ r, 0 < μ r) (ρ : Fin R → ℝ) (hρ : ∀ r, ρ r = ν r / μ r) :
    (∑ r, (w r / μ r) * ρ r ^ (-α) * n r ^ α * (ν r - μ r * (n r * x r)))
      = ∑ r, w r * ρ r ^ (-α) * n r ^ α * (ρ r - n r * x r) := by sorry

end KellyStochasticNetworks
