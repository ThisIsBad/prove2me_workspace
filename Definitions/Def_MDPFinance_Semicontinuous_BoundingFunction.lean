import Mathlib
import Definitions.Def_MDPFinance_Semicontinuous_Model

open MeasureTheory ProbabilityTheory

namespace MDPFinance.Semicontinuous

variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] {N : ℕ}

/-- An upper bounding function for the Markov Decision Model (Bäuerle–Rieder, Definition 2.4.1,
p. 28, PDF 43): a measurable `b : E → ℝ_+` for which there exist `c_r, c_g, α_b ∈ ℝ_+` with
`r_n^+(x,a) ≤ c_r b(x)` for `(x,a) ∈ D_n`, `g_N^+(x) ≤ c_g b(x)` for `x ∈ E`, and
`∫ b(x') Q_n(dx'|x,a) ≤ α_b b(x)` for `(x,a) ∈ D_n`, for every `n = 0, …, N-1`. Positive parts
`r_n^+`, `g_N^+` are written `max (·) 0`; the integral of the nonnegative `b` is the Lebesgue integral
`∫⁻`, so that (iii) also asserts its finiteness (a Bochner integral of a non-integrable `b` would be
`0`). -/
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

/-- `IB_b := {v ∈ IM(E) | |v(x)| ≤ c b(x)` for all `x`, for some `c ∈ ℝ_+}` (Bäuerle–Rieder,
p. 28, PDF 43), the second, equivalent form of the definition the book itself gives for the set
of functions of finite weighted supremum norm `‖·‖_b` — used directly rather than the norm
itself, which would need `EReal` division and its `0/0 := 0` convention for no further benefit
(see `MODERATION_NOTES.md`). -/
def IBb (b : E → ℝ) : Set (E → EReal) :=
  {v | Measurable v ∧ (∀ x, v x ≠ ⊤) ∧ ∃ c : ℝ, 0 ≤ c ∧ ∀ x, max (v x) (-(v x)) ≤ (c * b x : ℝ)}

/-- `IB_b^+ := {v ∈ IM(E) | v^+(x) ≤ c b(x)` for all `x`, for some `c ∈ ℝ_+}` (Bäuerle–Rieder,
p. 29, PDF 44), the standing regularity class for value functions throughout §2.4.1-2.4.3. -/
def IBbPlus (b : E → ℝ) : Set (E → EReal) :=
  {v | Measurable v ∧ (∀ x, v x ≠ ⊤) ∧ ∃ c : ℝ, 0 ≤ c ∧ ∀ x, (v x ⊔ 0) ≤ (c * b x : ℝ)}

end MDPFinance.Semicontinuous
