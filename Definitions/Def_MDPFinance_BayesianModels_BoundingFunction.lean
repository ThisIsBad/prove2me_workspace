import Mathlib
import Definitions.Def_MDPFinance_BayesianModels_Operators

open MeasureTheory ProbabilityTheory

namespace MDPFinance.BayesianModels

variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]

/-- An upper bounding function (Bäuerle–Rieder, Definition 2.4.1, p. 28, PDF 43, stationary):
a measurable `b : E → ℝ_{≥0}` with `r^+(x,a) ≤ c_r b(x)`, `g^+(x) ≤ c_g b(x)`, and
`∫ b(x') Q(dx'|x,a) ≤ α_b b(x)` (a Lebesgue integral, `b ≥ 0`, so that a `b` without finite
expectation cannot pass the bound with a default value). Restated from
`MDPFinance.Semicontinuous.IsUpperBoundingFunction` (chunk `02b`). -/
structure IsUpperBoundingFunction (D : Set (E × A)) (Q : E × A → Measure E) (r : E × A → EReal)
    (g : E → EReal) (b : E → ℝ) (cr cg αb : ℝ) : Prop where
  hb_meas : Measurable b
  hb_nonneg : ∀ x, 0 ≤ b x
  hcr : 0 ≤ cr
  hcg : 0 ≤ cg
  hαb : 0 ≤ αb
  hr : ∀ xa ∈ D, r xa ⊔ 0 ≤ ((cr * b xa.1 : ℝ) : EReal)
  hg : ∀ x, g x ⊔ 0 ≤ ((cg * b x : ℝ) : EReal)
  hQ : ∀ xa ∈ D, ∫⁻ x', ENNReal.ofReal (b x') ∂(Q xa) ≤ ENNReal.ofReal (αb * b xa.1)

/-- `IB_b^+ := {v ∈ IM(E) | v^+(x) ≤ c b(x)` for all `x`, for some `c ∈ ℝ_+}` (Bäuerle–Rieder,
p. 29, PDF 44). Restated from `MDPFinance.StructuredModels.IBbPlus` (chunk `02c`). -/
def IBbPlus (b : E → ℝ) : Set (E → EReal) :=
  {v | Measurable v ∧ (∀ x, v x ≠ ⊤) ∧ ∃ c : ℝ, 0 ≤ c ∧ ∀ x, (v x ⊔ 0) ≤ (c * b x : ℝ)}

end MDPFinance.BayesianModels
