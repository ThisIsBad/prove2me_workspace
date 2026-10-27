import Mathlib
import Definitions.Def_SinglePointPricing_Det_Setting

namespace SinglePointPricing.Det

open MeasureTheory

/-- Lemma 1 (Single Crossing Property), p. 17: for an `α`-strongly regular value law `F` on `[0, ∞)` and
`0 ≤ s ≤ s′` with `q_{s′} = F̄(s′) > 0` (and `q_s = F̄(s)`), the ccdf lies above the generalized
Pareto interpolant `q_s Γ_α(Γ_α^{−1}(q_{s′}/q_s)(v − s)/(s′ − s))` on `[s, s′]` and below it on
`(s′, +∞)`. -/
theorem lemma_1 (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : μ (Set.Iio 0) = 0) (hSR : IsAlphaSR α μ) (s s' : ℝ) (hs : 0 ≤ s) (hss' : s ≤ s')
    (hq : 0 < sf μ s') :
    (∀ v ∈ Set.Icc s s',
      sf μ s * GammaA α (GammaAInv α (sf μ s' / sf μ s) * (v - s) / (s' - s)) ≤ sf μ v) ∧
    (∀ v ∈ Set.Ioi s',
      sf μ v ≤ sf μ s * GammaA α (GammaAInv α (sf μ s' / sf μ s) * (v - s) / (s' - s))) := by sorry

end SinglePointPricing.Det

