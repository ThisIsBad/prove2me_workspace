import Mathlib
import Definitions.Def_MDPFinance_TerminalWealth_OnePeriod

open MeasureTheory ProbabilityTheory

namespace MDPFinance.TerminalWealth

/-- Theorem 4.1.1 (Bäuerle–Rieder, p. 77, PDF 91). In the one-period market of Section 4.1
(bond factor `1 + i > 0`, relative risk `R` with `𝔼‖R‖ < ∞`, the section's integrability
assumption), let `U` be a utility function with `domU = [0,∞)` or `domU = (0,∞)`. Then: a) there
are no arbitrage opportunities if and only if there exists a measurable `f* : domU → ℝ^d` such
that `u(x,f*(x)) = v(x)` for all `x ∈ domU`; b) `v` is strictly increasing, strictly concave and
continuous on `domU`. -/
theorem one_period_optimal_existence {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (measIP : Measure Ω) [IsProbabilityMeasure measIP] (domU : Set ℝ)
    (hdomU : domU = Set.Ici (0 : ℝ) ∨ domU = Set.Ioi (0 : ℝ)) (U : ℝ → ℝ)
    (hU : StrictMonoOn U domU ∧ StrictConcaveOn ℝ domU U ∧ ContinuousOn U domU)
    (i : ℝ) (hi : 0 < 1 + i) (R : Ω → Fin d → ℝ) (hR_meas : Measurable R)
    (hR_integrable : Integrable (fun ω => ∑ k, |R ω k|) measIP) :
    (NoArbitrageOnePeriod measIP R ↔
      ∃ fstar : ℝ → (Fin d → ℝ), Measurable fstar ∧
        ∀ x ∈ domU, OnePeriodU measIP U i R x (fstar x) = OnePeriodV measIP domU U i R x) ∧
      StrictMonoOn (OnePeriodV measIP domU U i R) domU ∧
      StrictConcaveOnEReal domU (OnePeriodV measIP domU U i R) ∧
      ContinuousOn (OnePeriodV measIP domU U i R) domU := by sorry

end MDPFinance.TerminalWealth
