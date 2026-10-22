import Mathlib
import Definitions.Def_ReedGGN_RenewalRep_Basic
import Definitions.Def_ReedGGN_RenewalRep_RenewalFunction

namespace ReedGGN.RenewalRep

open MeasureTheory

/-- (5.42)–(5.43), p. 29 (cited from Karlin–Taylor). Let `F` be the distribution function of a
probability measure `μ` carried by `[0, ∞)` with `F(0) = μ {0} < 1`, and let `H` be measurable
and bounded on every `[0, T]`. Then `r(t) = H(t) + ∫_{[0,t]} H(t − u) dM(u)` (5.43) is bounded
on every `[0, T]`, solves the renewal-type equation `r(t) = H(t) + ∫_{[0,t]} r(t − u) dF(u)` for
`t ≥ 0`, and every measurable solution bounded on every `[0, T]` agrees with it on `[0, ∞)`.
(The paper prints `∫_0^t r(t) dF(t − u)` in (5.42); the corrected form is stated.) -/
theorem renewal_type_equation (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ0 : μ (Set.Iio 0) = 0) (hatom : μ {0} < 1)
    (H : ℝ → ℝ) (hHm : Measurable H) (hHb : IsLocallyBounded H) :
    let r : ℝ → ℝ := fun t => H t + ∫ u in Set.Icc 0 t, H (t - u) ∂(renewalMeasure μ)
    IsLocallyBounded r ∧
    (∀ t : ℝ, 0 ≤ t → r t = H t + ∫ u in Set.Icc 0 t, r (t - u) ∂μ) ∧
    (∀ r' : ℝ → ℝ, Measurable r' → IsLocallyBounded r' →
      (∀ t : ℝ, 0 ≤ t → r' t = H t + ∫ u in Set.Icc 0 t, r' (t - u) ∂μ) →
      Set.EqOn r' r (Set.Ici 0)) := by sorry

end ReedGGN.RenewalRep

