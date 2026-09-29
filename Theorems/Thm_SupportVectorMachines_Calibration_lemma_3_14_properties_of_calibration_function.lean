import Mathlib
import Definitions.Def_SupportVectorMachines_Calibration_Loss
import Definitions.Def_SupportVectorMachines_Calibration_InnerRisks
import Definitions.Def_SupportVectorMachines_Calibration_CalibrationFunction

open MeasureTheory

namespace SupportVectorMachines.Calibration

/-- Lemma 3.14 (Properties of the calibration function), p. 58: for all `x ∈ X` and
`ε ∈ [0,∞]`: i) `M_{Lsur,Q,x}(δmax(ε,Q,x)) ⊆ M_{Ltar,Q,x}(ε)`; ii) `M_{Lsur,Q,x}(δ) ⊄
M_{Ltar,Q,x}(ε)` whenever `δ > δmax(ε,Q,x)`; and, if `C*_{Ltar,Q,x} < ∞` and `C*_{Lsur,Q,x} < ∞`,
Eq. (3.16): for all `t ∈ ℝ`,
`δmax(C_{Ltar,Q,x}(t) - C*_{Ltar,Q,x}, Q, x) ≤ C_{Lsur,Q,x}(t) - C*_{Lsur,Q,x}`. -/
theorem lemma_3_14_properties_of_calibration_function {X : Type*} (Ltar Lsur : Loss X)
    (Q : Measure ℝ) (x : X) (ε : ENNReal) :
    (approxMinimizers Lsur Q x (calibrationFunction Ltar Lsur Q x ε) ⊆
        approxMinimizers Ltar Q x ε) ∧
    (∀ δ : ENNReal, calibrationFunction Ltar Lsur Q x ε < δ →
      ¬ (approxMinimizers Lsur Q x δ ⊆ approxMinimizers Ltar Q x ε)) ∧
    (minInnerRisk Ltar Q x < ⊤ → minInnerRisk Lsur Q x < ⊤ →
      ∀ t : ℝ, calibrationFunction Ltar Lsur Q x
          (innerRisk Ltar Q x t - minInnerRisk Ltar Q x) ≤
        innerRisk Lsur Q x t - minInnerRisk Lsur Q x) := by sorry

end SupportVectorMachines.Calibration
