import Mathlib
import Definitions.Def_SmithRegenerative_Ergodic_Renewal

open MeasureTheory ProbabilityTheory Filter Topology

namespace SmithRegenerative.Ergodic

/-- **Renewal strong law** (Smith, *Regenerative stochastic processes*, Proc. R. Soc. Lond. A
232(1188):6–31 (1955), §5·3, proof of Lemma 8, p. 27, unnumbered): "It may easily be deduced
from renewal theory (see Doob, 1948) that n_t/t → μ₁⁻¹ with probability one."

The context of the sentence is Lemma 8: `t₀ = 0` and `μ₁ = E t₁ < ∞`.

Formalization Note: `t` is a renewal process (`IsRenewalProcess`: `t₁, t₂, …` i.i.d.,
non-negative, `P{t₁ = 0} < 1`) with delay `t₀ = 0` at every sample point; `μ₁ < ∞` is
integrability of `t₁`, and `μ₁ = ∫ t₁ dP`, which is strictly positive under the hypotheses (it
is not assumed separately). `n_t` is `count t t ω`, the number of `k ≥ 0` with `T_k ≤ t`. The
limit is along real `t → ∞`. -/
theorem count_div_tendsto {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (t : ℕ → Ω → ℝ) (hren : IsRenewalProcess P t)
    (ht0 : ∀ ω, t 0 ω = 0) (hμ : Integrable (t 1) P) :
    ∀ᵐ ω ∂P, Tendsto (fun s : ℝ => (count t s ω : ℝ) / s) atTop
      (𝓝 (∫ ω, t 1 ω ∂P)⁻¹) := by sorry

end SmithRegenerative.Ergodic

