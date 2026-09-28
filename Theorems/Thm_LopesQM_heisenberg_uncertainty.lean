import Mathlib
import Definitions.Def_LopesQM_Defs
open MeasureTheory

namespace LopesQM
theorem heisenberg_uncertainty {n : ℕ} (hbar : ℝ) (hhbar : 0 < hbar) (j : Fin n)
    (ψ : WaveFn n) (hX : InPositionDomain j ψ) (hP : InMomentumDomain ψ)
    (hnorm : l2Norm ψ = 1) :
    dispersion (positionOp j) ψ * dispersion (momentumOp hbar j) ψ ≥ hbar / 2 := by sorry
end LopesQM

