import Mathlib
import Definitions.Def_GomoryGroup_Rel_Setting

namespace GomoryGroup.Rel

open Matrix

theorem cost_identity {m n : ℕ} (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ)
    (cB : Fin m → ℝ) (cN : Fin n → ℝ) (b : Fin m → ℤ) (hB : B.det ≠ 0) :
    ∀ (xB : Fin m → ℝ) (xN : Fin n → ℝ),
      Br B *ᵥ xB + Nr N *ᵥ xN = (fun i => (b i : ℝ)) →
        cB ⬝ᵥ xB + cN ⬝ᵥ xN =
          cB ⬝ᵥ ((Br B)⁻¹ *ᵥ (fun i => (b i : ℝ))) + ∑ j, reducedCost B N cB cN j * xN j := by sorry

end GomoryGroup.Rel

