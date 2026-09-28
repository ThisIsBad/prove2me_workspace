import Mathlib
import Definitions.Def_LopesQM_Defs
open MeasureTheory

namespace LopesQM
theorem momentumOp_symmetric {n : ℕ} (hbar : ℝ) (j : Fin n) (ψ φ : WaveFn n)
    (hψ : InMomentumDomain ψ) (hφ : InMomentumDomain φ) :
    l2Inner (momentumOp hbar j ψ) φ = l2Inner ψ (momentumOp hbar j φ) := by sorry
end LopesQM

