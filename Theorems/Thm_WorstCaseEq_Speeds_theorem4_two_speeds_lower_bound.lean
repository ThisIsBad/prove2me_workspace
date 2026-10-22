import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_WorstCaseEq_Speeds_Model

namespace WorstCaseEq.Speeds

theorem theorem4_two_speeds_lower_bound (s₁ s₂ : ℝ) (h₁ : 0 < s₁) (h₁₂ : s₁ ≤ s₂)
    (hφ : s₂ ≤ Real.goldenRatio * s₁) :
    (∃ (n : ℕ) (w : Fin n → ℝ) (p : Fin n → Fin 2 → ℝ),
        (∀ i, 0 < w i) ∧ IsNash w ![s₁, s₂] p ∧ 0 < opt w ![s₁, s₂] ∧
          socialCost w ![s₁, s₂] p = (1 + s₂ / (s₁ + s₂)) * opt w ![s₁, s₂]) ∧
      1 + s₂ / (s₁ + s₂) ≤ Real.goldenRatio ∧
      (s₂ = Real.goldenRatio * s₁ → 1 + s₂ / (s₁ + s₂) = Real.goldenRatio) := by sorry

end WorstCaseEq.Speeds

