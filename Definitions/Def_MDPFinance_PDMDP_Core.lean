import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology

namespace MDPFinance.PDMDP

variable {E : Type*} [MeasurableSpace E]

/-- The extended-real integral, restated from `MDPFinance.Contracting.erealIntegral` (chunk
`07a`) per this chunk's own file-ownership boundary: a total, junk-safe stand-in for `∫ v dμ`
that is well-defined for every measurable `v : E → EReal`, used throughout this chunk for the
`IB_b^+`-valued (a priori not-yet-known-finite) side of the theory. -/
noncomputable def erealIntegral (μ : Measure E) (v : E → EReal) : EReal :=
  (↑(∫⁻ x, (v x ⊔ 0).toENNReal ∂μ) : EReal) + (-(↑(∫⁻ x, ((-v x) ⊔ 0).toENNReal ∂μ) : EReal))

/-- `IB_b^+ := \{v \in IM(E) \mid v^+(x) \le c\,b(x)\}` (Bäuerle–Rieder, p. 29, PDF 44, restated),
the `EReal`-valued regularity class the Continuity and Compactness Assumptions (Def. 8.2.4's
standing hypotheses) are stated against. -/
def IBbPlus (b : E → ℝ) : Set (E → EReal) :=
  {v | Measurable v ∧ (∀ x, v x ≠ ⊤) ∧ ∃ c : ℝ, 0 ≤ c ∧ ∀ x, (v x ⊔ 0) ≤ (c * b x : ℝ)}

end MDPFinance.PDMDP
