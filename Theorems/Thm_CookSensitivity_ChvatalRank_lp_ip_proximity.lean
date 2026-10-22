import Mathlib
import Definitions.Def_CookSensitivity_ChvatalRank_maxSubdet
import Definitions.Def_CookSensitivity_ChvatalRank_IntegerProgram

namespace CookSensitivity.ChvatalRank

open Matrix

theorem lp_ip_proximity {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (hA : A ≠ 0)
    (b : Fin m → ℚ) (w : Fin n → ℚ)
    (hint : ∃ x ∈ polyhedron A b, IsIntegral x)
    (hmax : ∃ x, IsLPOptimal A b w x) :
    (∀ xbar, IsLPOptimal A b w xbar →
      ∃ zstar, IsIPOptimal A b w zstar ∧
        supNorm (xbar - zstar) ≤ (n : ℚ) * (maxSubdet A : ℚ)) ∧
    (∀ zbar, IsIPOptimal A b w zbar →
      ∃ xstar, IsLPOptimal A b w xstar ∧
        supNorm (zbar - xstar) ≤ (n : ℚ) * (maxSubdet A : ℚ)) := by sorry

end CookSensitivity.ChvatalRank

