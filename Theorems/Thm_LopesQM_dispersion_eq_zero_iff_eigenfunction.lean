import Mathlib
import Definitions.Def_LopesQM_Defs
open MeasureTheory

namespace LopesQM
theorem dispersion_eq_zero_iff_eigenfunction {n : ℕ} (A : Op n) (ψ : WaveFn n)
    (hψ : MemLp ψ 2) (hAψ : MemLp (A ψ) 2) (hne : l2Norm ψ ≠ 0) :
    dispersion A ψ = 0 ↔ ∃ α : ℂ, A ψ =ᵐ[volume] fun x => α * ψ x := by sorry
end LopesQM

