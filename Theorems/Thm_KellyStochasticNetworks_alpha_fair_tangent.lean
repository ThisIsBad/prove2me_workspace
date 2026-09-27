import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_KellyStochasticNetworks_Congestion
import Definitions.Def_KellyStochasticNetworks_FlowLevel

namespace KellyStochasticNetworks

theorem alpha_fair_tangent {J R : ℕ} (A : Fin J → Fin R → ℝ) (C : Fin J → ℝ)
    (w n : Fin R → ℝ) (α : ℝ) (hα : 0 < α) (hw : ∀ r, 0 < w r) (hn : ∀ r, 0 < n r)
    (X U : Fin R → ℝ) (hXpos : ∀ r, 0 < X r) (hUpos : ∀ r, 0 < U r)
    (hXfeas : X ∈ networkFeasible A C) (hUfeas : U ∈ networkFeasible A C)
    (hmax : IsMaxOn (alphaFairObjective w n α)
      (networkFeasible A C ∩ {Y | ∀ r, 0 < Y r}) X) :
    (∑ r, w r * n r ^ α * U r ^ (-α) * (U r - X r)) ≤ 0 := by sorry

end KellyStochasticNetworks
