import Mathlib
import Definitions.Def_SmithRegenerative_CLT_CumulativeProcess

open MeasureTheory ProbabilityTheory Filter Topology

namespace SmithRegenerative.CLT

/-- Smith (1955), §5·3, proof of Lemma 8, p. 27 (unnumbered): "It may easily be deduced from
renewal theory (see Doob, 1948) that `n_t/t → μ₁⁻¹` with probability one."

For a renewal process with `t₀ = 0` and `μ₁ = E t₁ < ∞`, `n_t / t → 1/μ₁` almost surely as the
real time `t → ∞`. -/
theorem renewal_slln {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ) (hτ : IsRenewal P τ) (hμ : Integrable (τ 1) P) :
    ∀ᵐ ω ∂P, Tendsto (fun t : ℝ => (count τ t ω : ℝ) / t) atTop (𝓝 (mu1 P τ)⁻¹) := by sorry

end SmithRegenerative.CLT

