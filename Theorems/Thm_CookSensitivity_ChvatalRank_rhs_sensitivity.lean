import Mathlib
import Definitions.Def_CookSensitivity_ChvatalRank_maxSubdet
import Definitions.Def_CookSensitivity_ChvatalRank_IntegerProgram

namespace CookSensitivity.ChvatalRank

open Matrix

theorem rhs_sensitivity {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (b b' : Fin m → ℚ) (w : Fin n → ℚ)
    (hmax : ∃ x, IsLPOptimal A b w x) (hmax' : ∃ x, IsLPOptimal A b' w x) :
    (∀ xbar, IsLPOptimal A b w xbar →
      ∃ xbar', IsLPOptimal A b' w xbar' ∧
        supNorm (xbar - xbar') ≤ (n : ℚ) * (maxSubdet A : ℚ) * supNorm (b - b')) ∧
    ((∃ x ∈ polyhedron A b, IsIntegral x) → (∃ x ∈ polyhedron A b', IsIntegral x) →
      ∀ zbar, IsIPOptimal A b w zbar →
        ∃ zbar', IsIPOptimal A b' w zbar' ∧
          supNorm (zbar - zbar') ≤ (n : ℚ) * (maxSubdet A : ℚ) * (supNorm (b - b') + 2)) := by sorry

end CookSensitivity.ChvatalRank

