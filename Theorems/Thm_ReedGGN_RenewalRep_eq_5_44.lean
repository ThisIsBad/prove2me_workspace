import Mathlib
import Definitions.Def_ReedGGN_RenewalRep_Basic
import Definitions.Def_ReedGGN_RenewalRep_RenewalFunction
import Definitions.Def_ReedGGN_RenewalRep_Equations

namespace ReedGGN.RenewalRep

open MeasureTheory

/-- (5.44), p. 30: for a service law `μ`, a càdlàg driving path `ζ` and `β ∈ ℝ`, every càdlàg
solution `q` of the limit equation (5.33) satisfies, for every `t ≥ 0`,
`q(t) = ζ(t) + ∫_{[0,t]} ζ(t − u) dM(u) − β (F_e(t) + ∫_{[0,t]} F_e(t − s) dM(s))
  − ∫_{[0,t]} q⁻(t − u) dM(u)`, with `q⁻ = min(q, 0)`. -/
theorem eq_5_44 (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ0 : μ (Set.Iio 0) = 0) (hint : Integrable id μ) (hmean : ∫ x, x ∂μ = 1)
    (ζ : ℝ → ℝ) (hζ : ReedGGN.Regulator.IsCadlag ζ) (β : ℝ) (q : ℝ → ℝ) (hq : ReedGGN.Regulator.IsCadlag q)
    (hsol : SolvesLimitEq μ ζ β q) :
    ∀ t : ℝ, 0 ≤ t →
      q t = ζ t + (∫ u in Set.Icc 0 t, ζ (t - u) ∂(renewalMeasure μ))
        - β * (ReedGGN.Regulator.Fe μ t + ∫ s in Set.Icc 0 t, ReedGGN.Regulator.Fe μ (t - s) ∂(renewalMeasure μ))
        - ∫ u in Set.Icc 0 t, min (q (t - u)) 0 ∂(renewalMeasure μ) := by sorry

end ReedGGN.RenewalRep

