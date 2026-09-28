import Mathlib
import Definitions.Def_RobustSDP_Unstructured_Model

open Matrix
open scoped Matrix.Norms.L2Operator

namespace RobustSDP.Unstructured

/-- §5.1, p. 41, (21): minimizing the scalar `τ + ρ²(1 + ‖x‖²)/τ` over `τ > 0` turns the
Schur form of (20) into the single LMI `F(x) ⪰ 2ρ√(‖x‖² + 1) · I` of (21). -/
theorem eq_21 {m n : ℕ} (Fs : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ)
    (hFs : ∀ i, (Fs i).IsSymm) (ρ : ℝ) (hρ : 0 < ρ) (x : Fin m → ℝ) :
    (∃ τ : ℝ, 0 < τ ∧ (affineMap Fs x -
        (τ + ρ ^ 2 * (1 + ∑ i, x i ^ 2) / τ) • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef) ↔
      (affineMap Fs x -
        (2 * ρ * Real.sqrt (∑ i, x i ^ 2 + 1)) • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef := by sorry

end RobustSDP.Unstructured
