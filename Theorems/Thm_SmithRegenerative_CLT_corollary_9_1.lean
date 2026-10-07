import Mathlib
import Definitions.Def_SmithRegenerative_CLT_CumulativeProcess

open MeasureTheory ProbabilityTheory Filter Topology

namespace SmithRegenerative.CLT

/-- Smith (1955), Corollary 9·1, p. 30: "If `w_t` is a general cumulative process for which
`E(Δ_n w̃_t)² < ∞`, `κ₁ ≡ EΔ_n w_t`, `κ₂ ≡ E(Δ_n w_t)² < ∞`, and `σ² ≡ κ₂ − κ₁²`, then provided
`μ₁ < ∞`, `lim_{t=∞} P{(w_t − κ₁n_t)/(σ(t/μ₁)^{1/2}) ≤ α} = Φ(α)` (5·4·8). If, in addition,
`μ₂ < ∞`, then `lim_{t=∞} P{(w_t − (κ₁/μ₁)t)/((γt/μ₁)^{1/2}) ≤ α} = Φ(α)` (5·4·9), where
`γ = var Δ_n(w_t − κ₁μ₁⁻¹t)`."

For a cumulative process with `t₀ = 0`, `w₀ = 0` (the model with `M = 1`); the two assertions
are the two conjuncts, the second under `μ₂ = E t₁² < ∞`.

**Formalization Note** `σ > 0` and `γ > 0` are implicit (the paper divides by `σ` and `√γ`).
`Δ_n(w_t − κ₁μ₁⁻¹t) = y_n − (κ₁/μ₁) t_n`, so `γ = var(y₁ − (κ₁/μ₁) t₁)`. `n_t` is `count`.
`Φ = cdf (gaussianReal 0 1)`, and each limit is asserted for every real `α`. -/
theorem corollary_9_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ) (w : ℝ → Ω → ℝ) (hw : IsCumulativeModel P τ (fun _ : Fin 1 => w))
    (hμ : Integrable (τ 1) P)
    (hvar2 : Integrable (fun ω => varIncr w τ 1 ω ^ 2) P)
    (σ : ℝ) (hσ_pos : 0 < σ)
    (hσ : σ ^ 2 = (∫ ω, incr w τ 1 ω ^ 2 ∂P) - (∫ ω, incr w τ 1 ω ∂P) ^ 2) :
    (∀ α : ℝ, Tendsto
      (fun t : ℝ => P.real {ω | (w t ω - (∫ ω', incr w τ 1 ω' ∂P) * (count τ t ω : ℝ)) /
          (σ * Real.sqrt (t / mu1 P τ)) ≤ α})
      atTop (𝓝 (cdf (gaussianReal 0 1) α))) ∧
    (Integrable (fun ω => τ 1 ω ^ 2) P →
      ∀ γ : ℝ, 0 < γ →
        γ = variance (fun ω => incr w τ 1 ω - (∫ ω', incr w τ 1 ω' ∂P) / mu1 P τ * τ 1 ω) P →
        ∀ α : ℝ, Tendsto
          (fun t : ℝ => P.real {ω | (w t ω - (∫ ω', incr w τ 1 ω' ∂P) / mu1 P τ * t) /
              Real.sqrt (γ * t / mu1 P τ) ≤ α})
          atTop (𝓝 (cdf (gaussianReal 0 1) α))) := by sorry

end SmithRegenerative.CLT

