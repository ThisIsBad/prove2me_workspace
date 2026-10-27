import Mathlib
import Definitions.Def_CongestedPlatforms_Surge_Setting

namespace CongestedPlatforms.Surge

theorem proposition_3 (lam γ c : ℝ) (hlam : 0 < lam) (hc0 : 0 < c) (hc1 : c < 1)
    (hR : RegionA lam γ c ∨ RegionD lam γ c) :
    (∃ p : ℝ, IsSymNE lam γ 1 c p) ∧
    (∀ lamHat : ℝ, lam < lamHat → (RegionA lamHat γ c ∨ RegionD lamHat γ c) →
      (∃ q : ℝ, IsSymNE lamHat γ 1 c q) ∧
      ∀ p q : ℝ, IsSymNE lam γ 1 c p → IsSymNE lamHat γ 1 c q → ∀ v k : ℝ,
        uD0 lamHat γ 1 c v q < uD0 lam γ 1 c v p ∧
        uD1 lamHat γ 1 c v q < uD1 lam γ 1 c v p ∧
        uS lam γ 1 c k p < uS lamHat γ 1 c k q) ∧
    (∃ Λ : EReal, (lam : EReal) < Λ ∧
      ∀ lamHat : ℝ, lam < lamHat → (lamHat : EReal) ≤ Λ →
        (RegionA lamHat γ c ∨ RegionD lamHat γ c) →
        ∀ p q : ℝ, IsSymNE lam γ 1 c p → IsSymNE lamHat γ 1 c q → ∀ v k : ℝ,
          uD0 lamHat γ 1 c v p < uD0 lamHat γ 1 c v q ∧
          uD1 lamHat γ 1 c v p < uD1 lamHat γ 1 c v q ∧
          uS lamHat γ 1 c k p < uS lamHat γ 1 c k q) := by sorry

end CongestedPlatforms.Surge

