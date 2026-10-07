import Mathlib
import Definitions.Def_BurkholderDFI_ConvexPhi_Davis

namespace BurkholderDFI.ConvexPhi
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- (14.3), p. 33: the small-jump martingale's predictable jump bound. -/
theorem eq_14_3 {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}
    (hf : Martingale f ℱ P) :
    ∀ k, 1 ≤ k → ∀ᵐ ω ∂P,
      ENNReal.ofReal |davisA ℱ P f k ω| ≤
        4 * BurkholderDFI.SquareFnLp.maxFnN (BurkholderDFI.SquareFnLp.dseq f) (k - 1) ω := by sorry
end BurkholderDFI.ConvexPhi

