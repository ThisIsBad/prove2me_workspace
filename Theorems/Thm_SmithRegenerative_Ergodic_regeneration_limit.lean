import Mathlib
import Definitions.Def_SmithRegenerative_Ergodic_Renewal
import Definitions.Def_SmithRegenerative_Ergodic_CumulativeProcess

open MeasureTheory ProbabilityTheory Filter Topology

namespace SmithRegenerative.Ergodic

/-- **The ergodic limit along regeneration epochs** (Smith, *Regenerative stochastic processes*,
Proc. R. Soc. Lond. A 232(1188):6–31 (1955), §5·3, proof of Theorem 7, p. 27, unnumbered):
"Thus, from (5·3·3) and (5·3·4), lim_{t=∞} w_{t+Z_t}/t = κ₁/μ₁, with probability one."

Hypotheses are those of Theorem 7: `w_t` a cumulative process, `μ₁ < ∞`, `κ̃₁ < ∞`, `t₀ = 0`,
`w₀ = 0`.

Formalization Note: `t + Z_t = Σ_{i=1}^{n_t+1} t_i` is a regeneration epoch. `μ₁ < ∞` is
integrability of `t₁` and `κ̃₁ < ∞` integrability of `ỹ₁`; `μ₁ = ∫ t₁ dP` (strictly positive,
since `P{t₁ = 0} < 1`; not assumed separately) and `κ₁ = ∫ y₁ dP`. `w₀ = 0` holds at every
sample point. `IsCumulativeProcess` reads (C1) literally, with `ỹ_n` identically distributed and
no joint independence of `t` and `y`. The limit is along real `t → ∞`. -/
theorem regeneration_limit {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (t : ℕ → Ω → ℝ) (w : ℝ → Ω → ℝ) (hren : IsRenewalProcess P t)
    (ht0 : ∀ ω, t 0 ω = 0) (hw0 : ∀ ω, w 0 ω = 0) (hμ : Integrable (t 1) P)
    (hcum : IsCumulativeProcess P t w) (hκ : Integrable (cycleVariation t w 1) P) :
    ∀ᵐ ω ∂P, Tendsto (fun s : ℝ => w (s + Z t s ω) ω / s) atTop
      (𝓝 ((∫ ω, cycleIncrement t w 1 ω ∂P) / ∫ ω, t 1 ω ∂P)) := by sorry

end SmithRegenerative.Ergodic

