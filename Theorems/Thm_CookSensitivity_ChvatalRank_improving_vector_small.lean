import Mathlib
import Definitions.Def_CookSensitivity_ChvatalRank_maxSubdet
import Definitions.Def_CookSensitivity_ChvatalRank_IntegerProgram

namespace CookSensitivity.ChvatalRank

open Matrix

theorem improving_vector_small {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (hA : A ≠ 0)
    (b : Fin m → ℚ) (w : Fin n → ℚ)
    (z : Fin n → ℚ) (hz : IsIntegral z) (hzP : z ∈ polyhedron A b) :
    IsIPOptimal A b w z ∨
      ∃ zbar, IsIntegral zbar ∧ zbar ∈ polyhedron A b ∧
        supNorm (z - zbar) ≤ (n : ℚ) * (maxSubdet A : ℚ) ∧ w ⬝ᵥ zbar > w ⬝ᵥ z := by sorry

end CookSensitivity.ChvatalRank

