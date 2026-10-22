import Mathlib
import Definitions.Def_CookSensitivity_ChvatalRank_maxSubdet
import Definitions.Def_CookSensitivity_ChvatalRank_IntegerProgram

namespace CookSensitivity.ChvatalRank

open Matrix

theorem lp_ip_value_gap {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℚ) (w : Fin n → ℚ)
    (hint : ∃ x ∈ polyhedron A b, IsIntegral x)
    (xbar : Fin n → ℚ) (hxbar : IsLPOptimal A b w xbar) :
    ∃ zbar, IsIPOptimal A b w zbar ∧
      w ⬝ᵥ xbar - w ⬝ᵥ zbar ≤ (n : ℚ) * (maxSubdet A : ℚ) * l1Norm w := by sorry

end CookSensitivity.ChvatalRank

