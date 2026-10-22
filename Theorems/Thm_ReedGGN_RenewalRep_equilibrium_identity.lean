import Mathlib
import Definitions.Def_ReedGGN_RenewalRep_Basic
import Definitions.Def_ReedGGN_RenewalRep_RenewalFunction

namespace ReedGGN.RenewalRep

open MeasureTheory

/-- Proof of Corollary 5.2, p. 30 (unnumbered display before (5.45)): for a service law `μ`,
`F_e(t) + ∫_{[0,t]} F_e(t − s) dM(s) = t` for every `t ≥ 0`. -/
theorem equilibrium_identity (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ0 : μ (Set.Iio 0) = 0) (hint : Integrable id μ) (hmean : ∫ x, x ∂μ = 1) :
    ∀ t : ℝ, 0 ≤ t →
      ReedGGN.Regulator.Fe μ t + ∫ s in Set.Icc 0 t, ReedGGN.Regulator.Fe μ (t - s) ∂(renewalMeasure μ) = t := by sorry

end ReedGGN.RenewalRep

