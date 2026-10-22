import Mathlib
import Definitions.Def_ReedGGN_RenewalRep_Basic
import Definitions.Def_ReedGGN_RenewalRep_RenewalFunction

namespace ReedGGN.RenewalRep

open MeasureTheory

/-- The diffusion-limit equation (5.33), p. 25, for one sample path: with the driving path
`ζ = M̃_Q + Q̃_I` (5.40) and the Halfin–Whitt constant `β`,
`q(t) = ζ(t) − β F_e(t) + ∫_{[0,t]} q⁺(t − s) dF(s)` for every `t ≥ 0`,
where `q⁺ = max(q, 0)` and the integral is over the closed interval `[0, t]` against `μ`. -/
def SolvesLimitEq (μ : Measure ℝ) (ζ : ℝ → ℝ) (β : ℝ) (q : ℝ → ℝ) : Prop :=
  ∀ t, 0 ≤ t → q t = ζ t - β * ReedGGN.Regulator.Fe μ t + ∫ s in Set.Icc 0 t, max (q (t - s)) 0 ∂μ

/-- The renewal-function equation (5.41), p. 29, for one sample path:
`q(t) = ζ(t) + ∫_{[0,t]} ζ(t − u) dM(u) − β t − ∫_{[0,t]} q⁻(t − u) dM(u)` for every `t ≥ 0`,
where `q⁻ = min(q, 0) ≤ 0` (the paper's convention) and `dM` is `renewalMeasure μ`. -/
def SolvesRenewalEq (μ : Measure ℝ) (ζ : ℝ → ℝ) (β : ℝ) (q : ℝ → ℝ) : Prop :=
  ∀ t, 0 ≤ t → q t = ζ t + (∫ u in Set.Icc 0 t, ζ (t - u) ∂(renewalMeasure μ)) - β * t
    - ∫ u in Set.Icc 0 t, min (q (t - u)) 0 ∂(renewalMeasure μ)

end ReedGGN.RenewalRep
