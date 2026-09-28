import Mathlib
import Definitions.Def_LopesQM_Defs
open MeasureTheory

namespace LopesQM
theorem gaussianPacket_minimizes_uncertainty {n : ℕ} (hbar : ℝ) (hhbar : 0 < hbar)
    (a : ℝ) (ha : 0 < a) (x0 p0 : Rn n) (j : Fin n) :
    l2Norm (gaussianPacket hbar a x0 p0) = 1 ∧
    expectation (positionOp j) (gaussianPacket hbar a x0 p0) = ((x0 j : ℝ) : ℂ) ∧
    expectation (momentumOp hbar j) (gaussianPacket hbar a x0 p0) = ((p0 j : ℝ) : ℂ) ∧
    dispersion (positionOp j) (gaussianPacket hbar a x0 p0) = a ∧
    dispersion (positionOp j) (gaussianPacket hbar a x0 p0) *
      dispersion (momentumOp hbar j) (gaussianPacket hbar a x0 p0) = hbar / 2 := by sorry
end LopesQM

