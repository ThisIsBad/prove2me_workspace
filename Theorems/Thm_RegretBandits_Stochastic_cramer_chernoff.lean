import Mathlib
import Definitions.Def_RegretBandits_Stochastic_model

namespace RegretBandits.Stochastic

open MeasureTheory

/-- Eq. (2.3) of Bubeck and Cesa-Bianchi (arXiv:1204.5721v2, p. 10): if the rewards satisfy
(2.2) with a convex `ψ` (which is not below `ψ 0` on `(-∞, 0]`), then for every arm `i`, every
number of pulls `s ≥ 1` and every `ε ≥ 0`,
`ℙ(μ_i - μ̂_{i,s} > ε) ≤ e^{-s ψ*(ε)}`, with `e^{-∞} = 0`. -/
theorem cramer_chernoff {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {K : ℕ} (X : Fin K → ℕ → Ω → ℝ) (μ : Fin K → ℝ)
    (hX : IsStochasticBandit P X μ) (ψ : ℝ → ℝ) (hψ : SatisfiesMomentCondition P ψ X μ)
    (hψneg : ∀ l : ℝ, l ≤ 0 → ψ 0 ≤ ψ l) (i : Fin K) (s : ℕ) (hs : 1 ≤ s) (ε : ℝ)
    (hε : 0 ≤ ε) :
    P {ω | ε < μ i - sampleMean X i s ω} ≤
      EReal.exp (-((s : ℝ) : EReal) * legendreFenchel ψ ε) := by sorry

end RegretBandits.Stochastic

