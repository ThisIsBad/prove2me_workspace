import Mathlib
import Definitions.Def_GomoryGroup_Rel_Setting

namespace GomoryGroup.Rel

open Matrix

theorem ip_le_lp_add_group {m n : ℕ} (B : Matrix (Fin m) (Fin m) ℤ)
    (N : Matrix (Fin m) (Fin n) ℤ) (cB : Fin m → ℝ) (cN : Fin n → ℝ) (b : Fin m → ℤ)
    (hB : B.det ≠ 0) :
    ∀ φ : ℝ, IsGreatest (groupValues B N cB cN b) φ →
      ∀ (xB : Fin m → ℕ) (xN : Fin n → ℕ), IsIPFeasible B N b xB xN →
        ipCost cB cN xB xN ≤ cB ⬝ᵥ ((Br B)⁻¹ *ᵥ (fun i => (b i : ℝ))) + φ := by sorry

end GomoryGroup.Rel

