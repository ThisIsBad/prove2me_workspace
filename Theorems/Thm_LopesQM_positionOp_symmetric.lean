import Mathlib
import Definitions.Def_LopesQM_Defs
open MeasureTheory

namespace LopesQM
theorem positionOp_symmetric {n : ℕ} (j : Fin n) (ψ φ : WaveFn n)
    (hψ : InPositionDomain j ψ) (hφ : InPositionDomain j φ) :
    l2Inner (positionOp j ψ) φ = l2Inner ψ (positionOp j φ) := by sorry
end LopesQM

