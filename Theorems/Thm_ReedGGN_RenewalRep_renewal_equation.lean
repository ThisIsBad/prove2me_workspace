import Mathlib
import Definitions.Def_ReedGGN_RenewalRep_Basic
import Definitions.Def_ReedGGN_RenewalRep_RenewalFunction

namespace ReedGGN.RenewalRep

open MeasureTheory ProbabilityTheory

/-- (5.39), p. 29 (cited from Ross, Exercise 3.4). For a service law `μ` (probability measure
on `[0, ∞)` with mean `1`), the renewal function `M(t) = ∑_{n≥1} F^{∗n}(t)`
(a) is finite: `dM((-∞, t]) < ∞` for every `t`;
(b) solves the renewal equation `M(t) = F(t) + ∫_{[0,t]} M(t − u) dF(u)` for `t ≥ 0`;
(c) is its unique solution among measurable functions bounded on every `[0, T]`, on `[0, ∞)`. -/
theorem renewal_equation (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ0 : μ (Set.Iio 0) = 0) (hint : Integrable id μ) (hmean : ∫ x, x ∂μ = 1) :
    (∀ t : ℝ, renewalMeasure μ (Set.Iic t) < ⊤) ∧
    (∀ t : ℝ, 0 ≤ t →
      renewalFn μ t = cdf μ t + ∫ u in Set.Icc 0 t, renewalFn μ (t - u) ∂μ) ∧
    (∀ m : ℝ → ℝ, Measurable m → IsLocallyBounded m →
      (∀ t : ℝ, 0 ≤ t → m t = cdf μ t + ∫ u in Set.Icc 0 t, m (t - u) ∂μ) →
      Set.EqOn m (renewalFn μ) (Set.Ici 0)) := by sorry

end ReedGGN.RenewalRep

