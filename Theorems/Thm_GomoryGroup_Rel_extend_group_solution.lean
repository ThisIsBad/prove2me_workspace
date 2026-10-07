import Mathlib
import Definitions.Def_GomoryGroup_Rel_Setting

namespace GomoryGroup.Rel

open Matrix

theorem extend_group_solution {m n : ℕ} (B : Matrix (Fin m) (Fin m) ℤ)
    (N : Matrix (Fin m) (Fin n) ℤ) (cB : Fin m → ℝ) (cN : Fin n → ℝ) (b : Fin m → ℤ)
    (hB : B.det ≠ 0) :
    ∀ y : Fin n → ℕ, IsGroupOptimal B N cB cN b y →
      ∃ k : Fin m → ℤ, B *ᵥ k = b - N *ᵥ (fun j => (y j : ℤ)) ∧
        (0 ≤ k →
          IsIPOptimal B N cB cN b (fun i => (k i).toNat) y ∧
            ipCost cB cN (fun i => (k i).toNat) y =
              cB ⬝ᵥ ((Br B)⁻¹ *ᵥ (fun i => (b i : ℝ))) + groupObj B N cB cN y) := by sorry

end GomoryGroup.Rel

