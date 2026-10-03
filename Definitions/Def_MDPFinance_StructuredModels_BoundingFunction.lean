import Mathlib
import Definitions.Def_MDPFinance_StructuredModels_Model

open MeasureTheory ProbabilityTheory

namespace MDPFinance.StructuredModels

variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] {N : ℕ}

/-- An upper bounding function for the Markov Decision Model (Bäuerle–Rieder, Definition 2.4.1,
p. 28, PDF 43): a measurable `b : E → ℝ_+` for which there exist `c_r, c_g, α_b ∈ ℝ_+` with
`r_n^+(x,a) ≤ c_r b(x)` for `(x,a) ∈ D_n`, `g_N^+(x) ≤ c_g b(x)` for `x ∈ E`, and
`∫ b(x') Q_n(dx'|x,a) ≤ α_b b(x)` for `(x,a) ∈ D_n`, for every `n = 0, …, N-1`. Restated from
`MDPFinance.Semicontinuous.IsUpperBoundingFunction` (chunk `02b`). -/
structure IsUpperBoundingFunction (M : MarkovDecisionModel E A N) (b : E → ℝ)
    (cr cg αb : ℝ) : Prop where
  hb_meas : Measurable b
  hb_nonneg : ∀ x, 0 ≤ b x
  hcr : 0 ≤ cr
  hcg : 0 ≤ cg
  hαb : 0 ≤ αb
  hr : ∀ n < N, ∀ xa ∈ M.D n, max (M.r n xa) 0 ≤ cr * b xa.1
  hg : ∀ x, max (M.g x) 0 ≤ cg * b x
  hQ : ∀ n < N, ∀ xa ∈ M.D n,
    ∫⁻ x', ENNReal.ofReal (b x') ∂(M.Q n xa) ≤ ENNReal.ofReal (αb * b xa.1)

/-- `IB_b^+ := {v ∈ IM(E) | v^+(x) ≤ c b(x)` for all `x`, for some `c ∈ ℝ_+}` (Bäuerle–Rieder,
p. 29, PDF 44), the standing regularity class for value functions throughout §2.4. Restated from
`MDPFinance.Semicontinuous.IBbPlus` (chunk `02b`). -/
def IBbPlus (b : E → ℝ) : Set (E → EReal) :=
  {v | Measurable v ∧ (∀ x, v x ≠ ⊤) ∧ ∃ c : ℝ, 0 ≤ c ∧ ∀ x, (v x ⊔ 0) ≤ (c * b x : ℝ)}

end MDPFinance.StructuredModels
