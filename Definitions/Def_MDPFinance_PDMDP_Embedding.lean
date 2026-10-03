import Mathlib
import Definitions.Def_MDPFinance_PDMDP_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MDPFinance.PDMDP

variable {E U : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [MeasurableSpace U] [TopologicalSpace U]

/-- `r'_{rew}(x,α) := ∫_0^∞ e^{-(β+λ)t} rew(φ_t^α(x),α_t) dt ∈ [-∞,∞]` for a one-stage reward rate
`rew` (`rew = r` gives Eq. (8.5); `rew = r⁺` the positive part used by the Integrability
Assumption). -/
noncomputable def PDMDPModel.rprimeWith (Mk : PDMDPModel E U) (rew : E × U → ℝ)
    (xα : E × ControlFn U) : EReal :=
  erealIntegral (volume.restrict (Set.Ioi (0 : ℝ))) fun t =>
    ((Real.exp (-(Mk.β + Mk.lam) * t) * rew (Mk.φ t xα.2.1 xα.1, xα.2.1 t) : ℝ) : EReal)

/-- `r'(x,α) := ∫_0^∞ e^{-(β+λ)t} r(φ_t^α(x),α_t) dt` (Bäuerle–Rieder, Eq. (8.5), p. 247, PDF
258), the reward of the embedded discrete-time model (nonrelaxed controls), in `[-∞,∞]`. -/
noncomputable def PDMDPModel.rprime (Mk : PDMDPModel E U) (xα : E × ControlFn U) : EReal :=
  Mk.rprimeWith Mk.r xα

/-- The relaxed analogue of `rprimeWith`: `∫_0^∞ e^{-(β+λ)t} ∫_U rew(φRel_t^α(x),u) α_t(du) dt`
(Eq. (8.7)). -/
noncomputable def PDMDPModel.rprimeRelaxedWith (Mk : PDMDPModel E U) (rew : E × U → ℝ)
    (xα : E × RelaxedControlFn U) : EReal :=
  erealIntegral (volume.restrict (Set.Ioi (0 : ℝ))) fun t =>
    ((Real.exp (-(Mk.β + Mk.lam) * t) : ℝ) : EReal) *
      erealIntegral (xα.2.1 t).toMeasure fun u => ((rew (Mk.φRel t xα.2.1 xα.1, u) : ℝ) : EReal)

/-- `r'(x,α)` for relaxed controls (Bäuerle–Rieder, Eq. (8.7), p. 250, PDF 261). -/
noncomputable def PDMDPModel.rprimeRelaxed (Mk : PDMDPModel E U) (xα : E × RelaxedControlFn U) :
    EReal :=
  Mk.rprimeRelaxedWith Mk.r xα

/-- The **embedded discrete-time kernel** `Q'` (nonrelaxed controls), bundled as data: a
measurable family of measures (a kernel) satisfying `Q'(B|x,α) = λ ∫_0^∞ e^{-(λ+β)t}
Q(B|φ_t^α(x),α_t) dt` (Bäuerle–Rieder, Eq. (8.4), p. 247, PDF 258) on every measurable `B`. -/
structure EmbeddedKernel (Mk : PDMDPModel E U) where
  Qprime : E × ControlFn U → Measure E
  hQprime_meas : Measurable Qprime
  hQprime : ∀ xα (B : Set E), MeasurableSet B →
    Qprime xα B = ∫⁻ t in Set.Ioi (0 : ℝ),
      ENNReal.ofReal (Mk.lam * Real.exp (-(Mk.lam + Mk.β) * t)) *
        Mk.Q (Mk.φ t xα.2.1 xα.1, xα.2.1 t) B

/-- The relaxed analogue of `EmbeddedKernel`: `Q'(B|x,α) = λ ∫_0^∞ e^{-(λ+β)t} ∫_U
Q(B|φRel_t^α(x),u) α_t(du) dt` (Bäuerle–Rieder, Eq. (8.7), p. 250, PDF 261). -/
structure EmbeddedKernelRelaxed (Mk : PDMDPModel E U) where
  QprimeR : E × RelaxedControlFn U → Measure E
  hQprimeR_meas : Measurable QprimeR
  hQprimeR : ∀ xα (B : Set E), MeasurableSet B →
    QprimeR xα B = ∫⁻ t in Set.Ioi (0 : ℝ),
      ENNReal.ofReal (Mk.lam * Real.exp (-(Mk.lam + Mk.β) * t)) *
        ∫⁻ u, Mk.Q (Mk.φRel t xα.2.1 xα.1, u) B ∂(xα.2.1 t).toMeasure

end MDPFinance.PDMDP
