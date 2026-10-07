import Mathlib
import Definitions.Def_GomoryGroup_Rel_Setting

namespace GomoryGroup.Rel

open Matrix

theorem basic_part_nonneg {m n : ℕ} (B : Matrix (Fin m) (Fin m) ℤ)
    (N : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (hB : B.det ≠ 0)
    (hb : (fun i => (b i : ℝ)) ∈ reducedCone B (ell N * ((detD B : ℝ) - 1))) :
    ∀ y : Fin n → ℕ, ∑ j, y j ≤ detD B - 1 →
      euclNorm (Nr N *ᵥ (fun j => (y j : ℝ))) ≤ ((detD B : ℝ) - 1) * ell N ∧
        0 ≤ (Br B)⁻¹ *ᵥ ((fun i => (b i : ℝ)) - Nr N *ᵥ (fun j => (y j : ℝ))) := by sorry

end GomoryGroup.Rel

