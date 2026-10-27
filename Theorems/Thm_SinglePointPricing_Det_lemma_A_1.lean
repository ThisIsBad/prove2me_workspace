import Mathlib
import Definitions.Def_SinglePointPricing_Det_Setting

namespace SinglePointPricing.Det

/-- Lemma A-1, p. App-1: for `β > 0` and `s ≥ 0`, the generalized Pareto tail `v ↦ Γ_α(β(v − s))`
on `v ≥ s` has constant `α`-virtual value `(1 − α)v − F̄(v)/f(v) = (1 − α)s − 1/β`, where the density
`f` is minus the derivative of the tail. -/
theorem lemma_A_1 (α β s : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : 0 < β) (hs : 0 ≤ s) :
    ∀ v : ℝ, s ≤ v →
      (1 - α) * v - GammaA α (β * (v - s)) / (-deriv (fun x => GammaA α (β * (x - s))) v)
        = (1 - α) * s - 1 / β := by sorry

end SinglePointPricing.Det

