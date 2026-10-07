import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale
import Definitions.Def_BurkholderDFI_BMO_Condition

namespace BurkholderDFI.BMO

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- Theorem 19.1, p. 37: (19.1) gives the sharp exponential bound (19.2). -/
theorem theorem_19_1 {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}
    (hf : Martingale f ℱ P) (h191 : BMOCondition ℱ P f) :
    (∀ᵐ ω ∂P, BurkholderDFI.SquareFnLp.sqFn f ω ≠ ⊤) ∧
    ∀ t : ℝ, 0 < t → t < 1 →
      ∫⁻ ω, ENNReal.ofReal (Real.exp (t * ((BurkholderDFI.SquareFnLp.sqFn f ω).toReal) ^ 2)) ∂P
        ≤ ENNReal.ofReal ((1 - t)⁻¹) := by sorry

end BurkholderDFI.BMO

