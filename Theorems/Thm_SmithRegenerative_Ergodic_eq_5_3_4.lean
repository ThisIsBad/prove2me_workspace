import Mathlib
import Definitions.Def_SmithRegenerative_Ergodic_Renewal
import Definitions.Def_SmithRegenerative_Ergodic_CumulativeProcess

open MeasureTheory ProbabilityTheory Filter Topology

namespace SmithRegenerative.Ergodic

/-- **(5·3·4)** (Smith, *Regenerative stochastic processes*, Proc. R. Soc. Lond. A
232(1188):6–31 (1955), §5·3, proof of Theorem 7, p. 27): "But, by the strong law of large
numbers, lim_{t=∞} Σ₁^{n_t+1} y_i/(n_t + 1) = ν₁ (5·3·4) with probability one".

Formalization Note: the printed right-hand side "ν₁" is a misprint for `κ₁ = E y₁`: `ν₁ = E t₀`
(2·1·2) is `0` here, and the next display of the proof concludes `κ₁/μ₁`. The statement uses
`κ₁ = ∫ y₁ dP`. Hypotheses are those in force in the proof of Theorem 7 that the display needs:
a renewal process with `t₀ = 0` and `μ₁ < ∞` (integrability of `t₁`), a cumulative process `w`
(`IsCumulativeProcess`; (C1) read literally, no joint independence of `t` and `y`), and
`E|y₁| < ∞`, stated directly as integrability of `y₁`. The limit is along real `t → ∞`. -/
theorem eq_5_3_4 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (t : ℕ → Ω → ℝ) (w : ℝ → Ω → ℝ) (hren : IsRenewalProcess P t)
    (ht0 : ∀ ω, t 0 ω = 0) (hμ : Integrable (t 1) P) (hcum : IsCumulativeProcess P t w)
    (hκ : Integrable (cycleIncrement t w 1) P) :
    ∀ᵐ ω ∂P, Tendsto
      (fun s : ℝ => (∑ i ∈ Finset.Icc 1 (count t s ω + 1), cycleIncrement t w i ω) /
        ((count t s ω : ℝ) + 1))
      atTop (𝓝 (∫ ω, cycleIncrement t w 1 ω ∂P)) := by sorry

end SmithRegenerative.Ergodic

