import Mathlib
import Definitions.Def_CongestedPlatforms_Surge_Setting

namespace CongestedPlatforms.Surge

theorem proposition_1_d (lam γ c : ℝ) (hlam : 0 < lam) (hc0 : 0 < c) (hc : c < 1 / 2)
    (hD1 : γ < (1 / 2 - c) ^ 2 / (2 * lam)) (hD2 : lam / 2 ≤ γ) :
    (∀ p : ℝ, IsSymNE lam γ 1 c p ↔ p = c + Real.sqrt (lam * γ / 2)) ∧
    (lam < dP lam γ 1 c (c + Real.sqrt (lam * γ / 2)) + dP lam γ 1 c (c + Real.sqrt (lam * γ / 2))) ∧
    (lam / 2 < γ →
      D lam γ 1 c (c + Real.sqrt (lam * γ / 2)) (c + Real.sqrt (lam * γ / 2)) <
        S lam γ 1 c (c + Real.sqrt (lam * γ / 2)) (c + Real.sqrt (lam * γ / 2))) ∧
    (γ = lam / 2 →
      D lam γ 1 c (c + Real.sqrt (lam * γ / 2)) (c + Real.sqrt (lam * γ / 2)) =
        S lam γ 1 c (c + Real.sqrt (lam * γ / 2)) (c + Real.sqrt (lam * γ / 2))) := by sorry

end CongestedPlatforms.Surge

