import Mathlib
import Definitions.Def_SmithRegenerative_Moments_CumulativeProcess

namespace SmithRegenerative.Moments

open MeasureTheory Filter

/-- Smith, *Regenerative stochastic processes*, Proc. R. Soc. Lond. A
232(1188):6–31 (1955), p. 23, Lemma 4, (5·2·3).
Formalization Note: `Y_t` retains the upper index `n_t+1` of (5·2·1).
The printed intermediate identity (5·2·2) is off by one for this convention,
but the stated `o(t)` conclusion is unaffected. Integrability of `Y_t` is
made explicit instead of using Lean's zero default for a divergent integral. -/
theorem lemma_4_mean {Ω : Type*} [MeasurableSpace Ω]
    (C : CumulativeProcess Ω)
    (hμ : Integrable (C.renewal.cycleLength 1) C.renewal.P)
    (hκ : Integrable (cycleReward C.renewal C.w 1) C.renewal.P) :
    (∀ t : ℝ, 0 ≤ t → Integrable (C.overshootReward t) C.renewal.P) ∧
    (fun t : ℝ =>
      (∫ ω, C.overshootReward t ω ∂C.renewal.P) -
        C.meanReward / C.meanLength * t) =o[atTop] (fun t : ℝ => t) := by sorry

end SmithRegenerative.Moments

