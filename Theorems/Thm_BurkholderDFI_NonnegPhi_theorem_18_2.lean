import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace BurkholderDFI.NonnegPhi

/-- Theorem 18.2, p. 35: if `β > 1`, `0 < δ < (β² − 1)^{1/2}` and `f` is a nonnegative
martingale, then `P(S(f) > βλ, f^* ≤ δλ) ≤ 2δ²/(β² − δ² − 1) · P(S(f) > λ)` for all `λ > 0`. -/
theorem theorem_18_2 {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}
    (hf : Martingale f ℱ P) (hnn : ∀ n, 1 ≤ n → 0 ≤ᵐ[P] f n)
    (β δ : ℝ) (hβ : 1 < β) (hδ : 0 < δ) (hδβ : δ < Real.sqrt (β ^ 2 - 1))
    (l : ℝ) (hl : 0 < l) :
    P {ω | ENNReal.ofReal (β * l) < BurkholderDFI.SquareFnLp.sqFn f ω ∧ BurkholderDFI.SquareFnLp.maxFn f ω ≤ ENNReal.ofReal (δ * l)}
      ≤ ENNReal.ofReal (2 * δ ^ 2 / (β ^ 2 - δ ^ 2 - 1)) * P {ω | ENNReal.ofReal l < BurkholderDFI.SquareFnLp.sqFn f ω} := by sorry

end BurkholderDFI.NonnegPhi

