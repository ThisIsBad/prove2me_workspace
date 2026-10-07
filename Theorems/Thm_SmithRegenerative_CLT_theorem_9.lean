import Mathlib
import Definitions.Def_SmithRegenerative_CLT_CumulativeProcess

open MeasureTheory ProbabilityTheory Filter Topology

namespace SmithRegenerative.CLT

/-- Smith (1955), Theorem 9, p. 29: "If `E(Δ_n w̃_t)² < ∞`, `EΔ_n w_t = 0` and
`var Δ_n w_t = σ² < ∞`, then provided `μ₁ < ∞`, `lim_{t=∞} P{w_t/(σ(t/μ₁)^{1/2}) ≤ α} = Φ(α)`."

For a cumulative process with `t₀ = 0`, `w₀ = 0` (the model with `M = 1`).

**Formalization Note** `σ > 0` is implicit (the paper divides by `σ`); `σ` is the positive root
of `var y₁`. `E(Δ_n w̃)² < ∞` is integrability of `ỹ₁²`, which also makes `y₁` square
integrable, so `EΔ_n w_t` and `var Δ_n w_t` are genuine. `(t/μ₁)^{1/2}` is `Real.sqrt (t / μ₁)`.
`Φ = cdf (gaussianReal 0 1)`, and the limit is asserted for every real `α`. -/
theorem theorem_9 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ) (w : ℝ → Ω → ℝ) (hw : IsCumulativeModel P τ (fun _ : Fin 1 => w))
    (hμ : Integrable (τ 1) P)
    (hvar2 : Integrable (fun ω => varIncr w τ 1 ω ^ 2) P)
    (hmean : ∫ ω, incr w τ 1 ω ∂P = 0)
    (σ : ℝ) (hσ_pos : 0 < σ) (hσ : variance (incr w τ 1) P = σ ^ 2) :
    ∀ α : ℝ, Tendsto
      (fun t : ℝ => P.real {ω | w t ω / (σ * Real.sqrt (t / mu1 P τ)) ≤ α})
      atTop (𝓝 (cdf (gaussianReal 0 1) α)) := by sorry

end SmithRegenerative.CLT

