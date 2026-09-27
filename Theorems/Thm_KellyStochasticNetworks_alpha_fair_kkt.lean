import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_KellyStochasticNetworks_Congestion
import Definitions.Def_KellyStochasticNetworks_FlowLevel

namespace KellyStochasticNetworks

theorem alpha_fair_kkt {J R : ℕ} (A : Fin J → Fin R → ℝ) (C : Fin J → ℝ)
    (w n : Fin R → ℝ) (α : ℝ) (hα : 0 < α)
    (hA : ∀ j r, A j r = 0 ∨ A j r = 1) (hw : ∀ r, 0 < w r) (hn : ∀ r, 0 < n r)
    (x p : Fin R → ℝ) (q : Fin J → ℝ) (hxpos : ∀ r, 0 < x r)
    (hp : ∀ r, p r = ∑ j, A j r * q j) (hppos : ∀ r, 0 < p r)
    (hprimal : ∀ j, (∑ r, A j r * (n r * x r)) ≤ C j)
    (hdual : ∀ j, 0 ≤ q j)
    (hslack : ∀ j, q j * (C j - ∑ r, A j r * (n r * x r)) = 0)
    (hstat : ∀ r, x r = (w r / p r) ^ (1 / α)) :
    IsMaxOn (alphaFairObjective w n α)
      ({X | ∀ j, (∑ r, A j r * X r) ≤ C j} ∩ {X | ∀ r, 0 < X r})
      (fun r => n r * x r) := by sorry

end KellyStochasticNetworks
