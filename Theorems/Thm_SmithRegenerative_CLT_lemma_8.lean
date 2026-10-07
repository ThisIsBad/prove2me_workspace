import Mathlib
import Definitions.Def_SmithRegenerative_CLT_CumulativeProcess

open MeasureTheory ProbabilityTheory Filter Topology

namespace SmithRegenerative.CLT

/-- Smith (1955), Lemma 8, p. 26: "If `t₀ = 0`, `μ₁ < ∞`, and `κ̃_p < ∞` (`p > 0`), then
`lim_{t=∞} (w_{t+Z_t} − w_t)/t^{1/p} = 0`, with probability one."

For a cumulative process `w` (with `t₀ = 0`, `w₀ = 0`), `Z_t = Σ₁^{n_t+1} t_i − t` and
`κ̃_p = E ỹ₁^p`.

**Formalization Note** The single process is the model with `M = 1`. `t ^ (1/p)` is the real
power, positive for `t > 0`; `ỹ₁ ≥ 0` (a variation increment), so `ỹ₁ ^ p` is the real power of a
non-negative number. -/
theorem lemma_8 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ) (w : ℝ → Ω → ℝ) (hw : IsCumulativeModel P τ (fun _ : Fin 1 => w))
    (hμ : Integrable (τ 1) P) (p : ℝ) (hp : 0 < p)
    (hκp : Integrable (fun ω => varIncr w τ 1 ω ^ p) P) :
    ∀ᵐ ω ∂P, Tendsto (fun t : ℝ => (w (t + overshoot τ t ω) ω - w t ω) / t ^ (1 / p))
      atTop (𝓝 0) := by sorry

end SmithRegenerative.CLT

