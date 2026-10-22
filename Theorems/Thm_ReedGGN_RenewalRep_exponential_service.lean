import Mathlib
import Definitions.Def_ReedGGN_RenewalRep_Basic
import Definitions.Def_ReedGGN_RenewalRep_RenewalFunction
import Definitions.Def_ReedGGN_RenewalRep_Equations

namespace ReedGGN.RenewalRep

open MeasureTheory ProbabilityTheory

/-- p. 31, (5.46): for exponential service times of rate `1` (mean `1`),
(a) the renewal function is `M(t) = t` for `t ≥ 0`, as an identity of extended reals;
(b) for càdlàg `ζ` and `q` and `β ∈ ℝ`, (5.41) is equivalent to (5.46):
`q(t) = ζ(t) + ∫_0^t ζ(s) ds − β t − ∫_0^t q⁻(s) ds` for every `t ≥ 0`, `q⁻ = min(q, 0)`. -/
theorem exponential_service :
    (∀ t : ℝ, 0 ≤ t → renewalMeasure (expMeasure 1) (Set.Iic t) = ENNReal.ofReal t) ∧
    (∀ (ζ : ℝ → ℝ) (β : ℝ) (q : ℝ → ℝ), ReedGGN.Regulator.IsCadlag ζ → ReedGGN.Regulator.IsCadlag q →
      (SolvesRenewalEq (expMeasure 1) ζ β q ↔
        ∀ t : ℝ, 0 ≤ t →
          q t = ζ t + (∫ s in Set.Icc 0 t, ζ s) - β * t - ∫ s in Set.Icc 0 t, min (q s) 0)) := by sorry

end ReedGGN.RenewalRep

