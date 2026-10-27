import Mathlib
import Definitions.Def_CongestedPlatforms_Surge_Setting

namespace CongestedPlatforms.Surge

theorem proposition_1_a (lam γ c : ℝ) (hlam : 0 < lam) (hc0 : 0 < c) (hc1 : c < 1)
    (hA1 : (1 / 2 - c) ^ 2 / (2 * lam) ≤ γ ∨ 1 / 2 ≤ c) (hA2 : lam * (1 - c) / (1 + 2 * lam) ≤ γ) :
    (∀ p : ℝ, IsSymNE lam γ 1 c p ↔
      p = c + Real.sqrt (lam ^ 2 * γ ^ 2 + lam * γ * (1 - c)) - lam * γ) ∧
    (dP lam γ 1 c (c + Real.sqrt (lam ^ 2 * γ ^ 2 + lam * γ * (1 - c)) - lam * γ) +
        dP lam γ 1 c (c + Real.sqrt (lam ^ 2 * γ ^ 2 + lam * γ * (1 - c)) - lam * γ) ≤ lam) ∧
    (lam * (1 - c) / (1 + 2 * lam) < γ →
      D lam γ 1 c (c + Real.sqrt (lam ^ 2 * γ ^ 2 + lam * γ * (1 - c)) - lam * γ)
          (c + Real.sqrt (lam ^ 2 * γ ^ 2 + lam * γ * (1 - c)) - lam * γ) <
        S lam γ 1 c (c + Real.sqrt (lam ^ 2 * γ ^ 2 + lam * γ * (1 - c)) - lam * γ)
          (c + Real.sqrt (lam ^ 2 * γ ^ 2 + lam * γ * (1 - c)) - lam * γ)) ∧
    (γ = lam * (1 - c) / (1 + 2 * lam) →
      D lam γ 1 c (c + Real.sqrt (lam ^ 2 * γ ^ 2 + lam * γ * (1 - c)) - lam * γ)
          (c + Real.sqrt (lam ^ 2 * γ ^ 2 + lam * γ * (1 - c)) - lam * γ) =
        S lam γ 1 c (c + Real.sqrt (lam ^ 2 * γ ^ 2 + lam * γ * (1 - c)) - lam * γ)
          (c + Real.sqrt (lam ^ 2 * γ ^ 2 + lam * γ * (1 - c)) - lam * γ)) := by sorry

end CongestedPlatforms.Surge

