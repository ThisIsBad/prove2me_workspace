import Mathlib
import Definitions.Def_RobustSDP_Unstructured_Model

open Matrix
open scoped Matrix.Norms.L2Operator

namespace RobustSDP.Unstructured

/-- §5.1, p. 41, paragraph after (20): every feasible `τ` in (20) is strictly
positive, and by Schur complements (20) is equivalent to `F(x) ⪰ (τ + ρ²(1 + ‖x‖²)/τ) I`, `τ > 0`,
where `‖x‖² = ∑ᵢ xᵢ²` is the squared Euclidean norm. -/
theorem tau_pos_schur {m n : ℕ} (hn : 0 < n) (Fs : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ)
    (hFs : ∀ i, (Fs i).IsSymm) (ρ : ℝ) (hρ : 0 < ρ) (τ : ℝ) (x : Fin m → ℝ) :
    (lmi20 Fs ρ τ x).PosSemidef ↔
      0 < τ ∧ (affineMap Fs x -
        (τ + ρ ^ 2 * (1 + ∑ i, x i ^ 2) / τ) • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef := by sorry

end RobustSDP.Unstructured
