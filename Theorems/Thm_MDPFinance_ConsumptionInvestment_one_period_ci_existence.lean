import Mathlib
import Definitions.Def_MDPFinance_ConsumptionInvestment_OnePeriod

open MeasureTheory ProbabilityTheory

namespace MDPFinance.ConsumptionInvestment

/-- Theorem 4.3.1 (Bäuerle–Rieder, p. 95, PDF 109). In the one-period market (bond factor
`1 + i > 0`, `𝔼‖R‖ < ∞`), let `Uc` and `Up` be utility functions with `domUc = domUp = [0,∞)`.
Then: a) there are no arbitrage opportunities iff there is a measurable
`f* : domUp → ℝ_{\ge0} × ℝ^d` with `u(x,f*(x)) = v(x)` for all `x ∈ domUp`; b) `v` is strictly
increasing, strictly concave and continuous on `domUp`. -/
theorem one_period_ci_existence {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (measIP : Measure Ω) [IsProbabilityMeasure measIP] (domUp : Set ℝ)
    (hdomUp : domUp = Set.Ici (0 : ℝ)) (Uc Up : ℝ → ℝ)
    (hUc : StrictMonoOn Uc domUp ∧ StrictConcaveOn ℝ domUp Uc ∧ ContinuousOn Uc domUp)
    (hUp : StrictMonoOn Up domUp ∧ StrictConcaveOn ℝ domUp Up ∧ ContinuousOn Up domUp)
    (i : ℝ) (hi : 0 < 1 + i) (R : Ω → Fin d → ℝ) (hR_meas : Measurable R)
    (hR_integrable : Integrable (fun ω => ∑ k, |R ω k|) measIP) :
    (NoArbitrageOnePeriodCI measIP R ↔
      ∃ fstar : ℝ → ℝ × (Fin d → ℝ), Measurable fstar ∧
        ∀ x ∈ domUp, OnePeriodCIU measIP Uc Up i R x (fstar x) =
          OnePeriodCIV measIP domUp Uc Up i R x) ∧
      StrictMonoOn (OnePeriodCIV measIP domUp Uc Up i R) domUp ∧
      StrictConcaveOnEReal domUp (OnePeriodCIV measIP domUp Uc Up i R) ∧
      ContinuousOn (OnePeriodCIV measIP domUp Uc Up i R) domUp := by sorry

end MDPFinance.ConsumptionInvestment
