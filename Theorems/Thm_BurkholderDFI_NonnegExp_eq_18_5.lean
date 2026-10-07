import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

namespace BurkholderDFI.NonnegExp
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

/-- (18.5), p. 37: the tail integral after the stopping threshold. -/
theorem eq_18_5 {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}
    (hf : Martingale f ℱ P) (hnn : ∀ n, 1 ≤ n → 0 ≤ᵐ[P] f n)
    (l : ℝ) (hl : 0 < l) (a : ℝ) (ha : 0 < a) :
    ∫⁻ s in Set.Ioi (a + l ^ 2), P {ω | ENNReal.ofReal s < BurkholderDFI.SquareFnLp.sqFnAt f (BurkholderDFI.SquareFnLp.exitTime f l ω - 1) ω ^ 2}
      ≤ ENNReal.ofReal (2 * l ^ 2) * P {ω | ENNReal.ofReal a < BurkholderDFI.SquareFnLp.sqFnAt f (BurkholderDFI.SquareFnLp.exitTime f l ω - 1) ω ^ 2} := by sorry

end BurkholderDFI.NonnegExp

