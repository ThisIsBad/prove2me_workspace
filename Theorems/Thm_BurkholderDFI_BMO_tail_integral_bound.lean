import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale
import Definitions.Def_BurkholderDFI_BMO_Condition

namespace BurkholderDFI.BMO

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- §19, proof of Theorem 19.1, p. 37: the tail integral of `S(f)²` under (19.1). -/
theorem tail_integral_bound {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}
    (hf : Martingale f ℱ P) (h191 : BMOCondition ℱ P f) :
    ∀ a : ℝ, 0 < a →
      ∫⁻ x in Set.Ioi a, P {ω | ENNReal.ofReal x < BurkholderDFI.SquareFnLp.sqFn f ω ^ 2}
        ≤ P {ω | ENNReal.ofReal a < BurkholderDFI.SquareFnLp.sqFn f ω ^ 2} := by sorry

end BurkholderDFI.BMO

