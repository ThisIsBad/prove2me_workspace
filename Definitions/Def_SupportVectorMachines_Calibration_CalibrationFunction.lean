import Mathlib
import Definitions.Def_SupportVectorMachines_Calibration_Loss
import Definitions.Def_SupportVectorMachines_Calibration_InnerRisks

open MeasureTheory

namespace SupportVectorMachines.Calibration

/-- The **calibration function** `δmax(·,Q,x)` of `(Ltar, Lsur)` (Steinwart & Christmann,
*Support Vector Machines*, Springer 2008, Definition 3.13, p. 58): for `ε ∈ [0,∞]`,
`δmax(ε,Q,x) := inf_{t ∉ M_{Ltar,Q,x}(ε)} C_{Lsur,Q,x}(t) - C*_{Lsur,Q,x}` if `C*_{Lsur,Q,x} < ∞`,
and `δmax(ε,Q,x) := ∞` otherwise. The infimum over the empty set (when `M_{Ltar,Q,x}(ε) = ℝ`) is
`⊤` by the ambient `ENNReal` convention, matching the book's own reading of an empty infimum. -/
noncomputable def calibrationFunction {X : Type*} (Ltar Lsur : Loss X) (Q : Measure ℝ) (x : X)
    (ε : ENNReal) : ENNReal :=
  if minInnerRisk Lsur Q x = ⊤ then ⊤
  else (⨅ t ∈ {t : ℝ | t ∉ approxMinimizers Ltar Q x ε}, innerRisk Lsur Q x t) -
    minInnerRisk Lsur Q x

/-- `Lsur` **is `Ltar`-calibrated with respect to `𝒬`** (Definition 3.18, p. 61): for all
`ε ∈ (0,∞]`, `Q ∈ 𝒬`, and `x ∈ X`, `δmax(ε,Q,x) > 0`. -/
def IsCalibrated {X : Type*} (Ltar Lsur : Loss X) (𝒬 : Set (Measure ℝ)) : Prop :=
  ∀ ε : ENNReal, 0 < ε → ∀ Q ∈ 𝒬, ∀ x : X, 0 < calibrationFunction Ltar Lsur Q x ε

end SupportVectorMachines.Calibration
