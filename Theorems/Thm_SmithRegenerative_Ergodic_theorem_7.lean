import Mathlib
import Definitions.Def_SmithRegenerative_Ergodic_Renewal
import Definitions.Def_SmithRegenerative_Ergodic_CumulativeProcess

open MeasureTheory ProbabilityTheory Filter Topology

namespace SmithRegenerative.Ergodic

/-- **Theorem 7 (the ergodic theorem)** (Smith, *Regenerative stochastic processes*, Proc. R.
Soc. Lond. A 232(1188):6–31 (1955), §5·3, p. 27): "If w_t is a cumulative process (satisfying
(C1) and (C2)); and if μ₁ < ∞ and κ̃₁ < ∞; and if t₀ = 0 and we define w₀ = 0, then
lim_{t=∞} w_t/t = κ₁/μ₁ with probability one."

Formalization Note: `t` is the general renewal process `t₀, t₁, …` (`IsRenewalProcess`: `t₁, t₂,
…` i.i.d., non-negative, `P{t₁ = 0} < 1`) with `t₀ = 0` at every sample point; `w` is a real
process with `w₀ = 0` at every sample point. `IsCumulativeProcess` is (C1) read literally (the
cycle increments `y_n = w_{T_n} − w_{T_{n−1}}` i.i.d.), (C2) (almost every path of bounded
variation on every `[0, s]`), and the cycle variations `ỹ_n` identically distributed (the
paper's notation `κ̃_r` presupposes it); no joint independence of cycle lengths and increments
is assumed. `μ₁ < ∞` is integrability of `t₁`, `κ̃₁ < ∞` integrability of `ỹ₁`;
`μ₁ = ∫ t₁ dP` is strictly positive under the hypotheses and is not assumed positive separately;
`κ₁ = ∫ y₁ dP` (`y₁` is integrable since `|y₁| ≤ ỹ₁` almost surely). The limit is along real
`t → ∞`. -/
theorem theorem_7 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (t : ℕ → Ω → ℝ) (w : ℝ → Ω → ℝ) (hren : IsRenewalProcess P t)
    (ht0 : ∀ ω, t 0 ω = 0) (hw0 : ∀ ω, w 0 ω = 0) (hμ : Integrable (t 1) P)
    (hcum : IsCumulativeProcess P t w) (hκ : Integrable (cycleVariation t w 1) P) :
    ∀ᵐ ω ∂P, Tendsto (fun s : ℝ => w s ω / s) atTop
      (𝓝 ((∫ ω, cycleIncrement t w 1 ω ∂P) / ∫ ω, t 1 ω ∂P)) := by sorry

end SmithRegenerative.Ergodic

