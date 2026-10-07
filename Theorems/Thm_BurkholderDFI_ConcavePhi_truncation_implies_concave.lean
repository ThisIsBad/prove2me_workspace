import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace BurkholderDFI.ConcavePhi

/-- §20, proof of Theorem 20.1, p. 38: "Inequality (20.2) is a special case of (20.1) but actually
implies (20.1)." Stated for arbitrary measurable `[0, ∞]`-valued `Z`, `W`: if
`E(Z ∧ λ) ≤ 2E(W ∧ λ)` for every `λ > 0`, then `EΦ(Z) ≤ 2EΦ(W)` for every concave `Φ` satisfying
the conditions of Section 7. -/
theorem truncation_implies_concave {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (Φ : ℝ≥0∞ → ℝ≥0∞) (c : ℝ≥0) (hΦ : BurkholderDFI.SquareFnLp.IsPhi Φ c)
    (hcc : BurkholderDFI.SquareFnLp.IsConcavePhi Φ) (Z W : Ω → ℝ≥0∞) (hZ : Measurable Z) (hW : Measurable W)
    (h202 : ∀ l : ℝ≥0, 0 < l →
      ∫⁻ ω, min (Z ω) (l : ℝ≥0∞) ∂P ≤ 2 * ∫⁻ ω, min (W ω) (l : ℝ≥0∞) ∂P) :
    ∫⁻ ω, Φ (Z ω) ∂P ≤ 2 * ∫⁻ ω, Φ (W ω) ∂P := by sorry

end BurkholderDFI.ConcavePhi

