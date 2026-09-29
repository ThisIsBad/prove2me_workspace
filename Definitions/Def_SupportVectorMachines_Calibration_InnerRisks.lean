import Mathlib
import Definitions.Def_SupportVectorMachines_Calibration_Loss

open MeasureTheory

namespace SupportVectorMachines.Calibration

/-- The **inner `L`-risk** of `Q` at `x` (Steinwart & Christmann, *Support Vector Machines*,
Springer 2008, Definition 3.3, p. 52): for a loss `L`, a distribution `Q` on the label space
`ℝ`, a point `x ∈ X` and `t ∈ ℝ`, `C_{L,Q,x}(t) := ∫_Y L(x,y,t) dQ(y)`, represented as a lower
Lebesgue integral into `[0,∞]` (always well-defined for the nonnegative integrand `L`, no
integrability hypothesis needed). -/
noncomputable def innerRisk {X : Type*} (L : Loss X) (Q : Measure ℝ) (x : X) (t : ℝ) : ENNReal :=
  ∫⁻ y, ENNReal.ofReal (L x y t) ∂Q

/-- The **minimal inner `L`-risk** of `Q` at `x` (Definition 3.3, p. 52):
`C*_{L,Q,x} := inf_{t∈ℝ} C_{L,Q,x}(t)`. -/
noncomputable def minInnerRisk {X : Type*} (L : Loss X) (Q : Measure ℝ) (x : X) : ENNReal :=
  ⨅ t : ℝ, innerRisk L Q x t

/-- The set of **`ε`-approximate minimizers** of `C_{L,Q,x}(·)` (Definition 3.5, p. 53):
`M_{L,Q,x}(ε) := {t ∈ ℝ : C_{L,Q,x}(t) < C*_{L,Q,x} + ε}`. -/
def approxMinimizers {X : Type*} (L : Loss X) (Q : Measure ℝ) (x : X) (ε : ENNReal) : Set ℝ :=
  {t : ℝ | innerRisk L Q x t < minInnerRisk L Q x + ε}

end SupportVectorMachines.Calibration
