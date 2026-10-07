import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

namespace BurkholderDFI.NonnegExp
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

/-- Theorem 18.1, p. 35: exponential square integrability of the stopped square function. -/
theorem theorem_18_1 {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}
    (hf : Martingale f ℱ P) (hnn : ∀ n, 1 ≤ n → 0 ≤ᵐ[P] f n) (l : ℝ) (hl : 0 < l) :
    (∀ᵐ ω ∂P, BurkholderDFI.SquareFnLp.sqFnAt f (BurkholderDFI.SquareFnLp.exitTime f l ω - 1) ω ≠ ⊤) ∧
    ∀ t : ℝ, 0 < t → t < 1 / (3 * l ^ 2) →
      ∫⁻ ω, ENNReal.ofReal (Real.exp (t * ((BurkholderDFI.SquareFnLp.sqFnAt f (BurkholderDFI.SquareFnLp.exitTime f l ω - 1) ω).toReal) ^ 2)) ∂P
        ≤ ENNReal.ofReal (1 / (1 - 3 * t * l ^ 2)) := by sorry

end BurkholderDFI.NonnegExp

