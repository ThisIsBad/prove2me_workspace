import Mathlib
import Definitions.Def_MDPFinance_PDMDP_Model
import Definitions.Def_MDPFinance_PDMDP_Core

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MDPFinance.PDMDP

variable {E U : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [MeasurableSpace U] [TopologicalSpace U] [OpensMeasurableSpace U]

/-- Definition 8.2.4 (Bäuerle–Rieder, p. 251, PDF 262): a measurable `b : E → ℝ_{≥0}` is an
**upper bounding function** if there are `c_r, c_Q, c_φ ≥ 0` with (i) `r⁺(x,u) ≤ c_r b(x)`,
(ii) `∫ b(z) Q(dz|x,u) ≤ c_Q b(x)`, (iii) `λ ∫_0^∞ e^{-(λ+β)t} b(φ_t^α(x)) dt ≤ c_φ b(x)` for all
`x` and all **relaxed** `α ∈ R` (Lebesgue integrals, `b ≥ 0`). Then `α_b ≤ c_Q c_φ` for the
embedded model. -/
structure IsUpperBoundingFunctionPDMDP (Mk : PDMDPModel E U) (b : E → ℝ) (cr cQ cφ : ℝ) :
    Prop where
  hb_meas : Measurable b
  hb_nonneg : ∀ x, 0 ≤ b x
  hcr : 0 ≤ cr
  hcQ : 0 ≤ cQ
  hcφ : 0 ≤ cφ
  hr : ∀ x u, max (Mk.r (x, u)) 0 ≤ cr * b x
  hQ : ∀ x u, ∫⁻ z, ENNReal.ofReal (b z) ∂(Mk.Q (x, u)) ≤ ENNReal.ofReal (cQ * b x)
  hφ : ∀ x (α : ℝ → ProbabilityMeasure U), Measurable α →
    (∫⁻ t in Set.Ioi (0 : ℝ),
      ENNReal.ofReal (Mk.lam * Real.exp (-(Mk.lam + Mk.β) * t) * b (Mk.φRel t α x))) ≤
      ENNReal.ofReal (cφ * b x)

/-- A **bounding function** (Bäuerle–Rieder, p. 255, PDF 266: "an upper bounding function with
`r` replaced by `|r|`"). -/
structure IsBoundingFunctionPDMDP (Mk : PDMDPModel E U) (b : E → ℝ) (cr cQ cφ : ℝ) :
    Prop where
  hb_meas : Measurable b
  hb_nonneg : ∀ x, 0 ≤ b x
  hcr : 0 ≤ cr
  hcQ : 0 ≤ cQ
  hcφ : 0 ≤ cφ
  hr : ∀ x u, |Mk.r (x, u)| ≤ cr * b x
  hQ : ∀ x u, ∫⁻ z, ENNReal.ofReal (b z) ∂(Mk.Q (x, u)) ≤ ENNReal.ofReal (cQ * b x)
  hφ : ∀ x (α : ℝ → ProbabilityMeasure U), Measurable α →
    (∫⁻ t in Set.Ioi (0 : ℝ),
      ENNReal.ofReal (Mk.lam * Real.exp (-(Mk.lam + Mk.β) * t) * b (Mk.φRel t α x))) ≤
      ENNReal.ofReal (cφ * b x)

/-- The **Continuity and Compactness Assumptions** of §8.2 (Bäuerle–Rieder, p. 251, PDF 262),
with `R` carrying the Young topology: (i) `U` compact, (ii) `(t,x,α) ↦ φ_t^α(x)` continuous on
`ℝ₊ × E × R`, (iii) `(x,α) ↦ ∫_0^∞ e^{-(λ+β)t} b(φ_t^α(x)) dt` continuous on `E × R`, (iv)
`(x,u) ↦ ∫ v(z) Q(dz|x,u)` upper semicontinuous for all usc `v ∈ IB_b^+`, (v) `r` upper
semicontinuous. -/
def ContinuityCompactnessAssumptions (Mk : PDMDPModel E U) (b : E → ℝ) : Prop :=
  IsCompact (Set.univ : Set U) ∧
  (letI : TopologicalSpace (ℝ → ProbabilityMeasure U) := youngTopology U;
    ContinuousOn (fun p : ℝ × (ℝ → ProbabilityMeasure U) × E => Mk.φRel p.1 p.2.1 p.2.2)
      {p | 0 ≤ p.1}) ∧
  (letI : TopologicalSpace (ℝ → ProbabilityMeasure U) := youngTopology U;
    Continuous (fun p : E × (ℝ → ProbabilityMeasure U) =>
      ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(Mk.lam + Mk.β) * t) * b (Mk.φRel t p.2 p.1))) ∧
  (∀ v ∈ IBbPlus b, UpperSemicontinuous v →
    UpperSemicontinuous fun p : E × U => erealIntegral (Mk.Q p) v) ∧
  UpperSemicontinuous Mk.r

end MDPFinance.PDMDP
