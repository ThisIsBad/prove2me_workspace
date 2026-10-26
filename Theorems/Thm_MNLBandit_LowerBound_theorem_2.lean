import Mathlib
import Definitions.Def_MNLBandit_LowerBound_Setting

namespace MNLBandit.LowerBound

theorem theorem_2 :
    ∃ C : ℝ, 0 < C ∧ ∀ (n K T : ℕ), 2 ≤ n → 1 ≤ K → K ≤ n → n ≤ T →
      ∃ (m : ℕ) (w : Fin m → ℝ) (inst : Fin m → Instance n),
        (∀ j, 0 ≤ w j) ∧ ∑ j, w j = 1 ∧ (∀ j, (inst j).Valid) ∧
        (∀ j k, (inst j).v₀ = (inst k).v₀ ∧ (inst j).r = (inst k).r) ∧
        ∀ π : BPolicy n, IsCardinalityK K π →
          C * Real.sqrt ((n : ℝ) * T / K) ≤ ∑ j, w j * regret (inst j) K π T := by sorry

end MNLBandit.LowerBound

