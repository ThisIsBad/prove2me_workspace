import Mathlib
import Definitions.Def_LopesQM_Defs
open MeasureTheory

namespace LopesQM
theorem canonical_commutation_relations {n : ℕ} (hbar : ℝ) (hhbar : 0 < hbar) (j k : Fin n) :
    (∀ ψ : WaveFn n, ∀ x : Rn n,
        commutator (positionOp k) (positionOp j) ψ x = 0) ∧
    (∀ ψ : WaveFn n, ContDiff ℝ 2 ψ → ∀ x : Rn n,
        commutator (momentumOp hbar k) (momentumOp hbar j) ψ x = 0) ∧
    (∀ ψ : WaveFn n, Differentiable ℝ ψ → ∀ x : Rn n,
        Complex.I / (hbar : ℂ) * commutator (momentumOp hbar j) (positionOp j) ψ x = ψ x) ∧
    (j ≠ k → ∀ ψ : WaveFn n, Differentiable ℝ ψ → ∀ x : Rn n,
        Complex.I / (hbar : ℂ) * commutator (momentumOp hbar j) (positionOp k) ψ x = 0) := by sorry
end LopesQM

