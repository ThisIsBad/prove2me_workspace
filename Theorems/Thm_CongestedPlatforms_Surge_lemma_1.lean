import Mathlib
import Definitions.Def_CongestedPlatforms_Surge_Setting

namespace CongestedPlatforms.Surge

theorem lemma_1 (lam γ α c p0 p1 : ℝ) (hlam : 0 < lam) (hγ : 0 < γ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hc : 0 ≤ c) (hx0 : 0 < α * p0 - c) (hx1 : 0 < α * p1 - c) (hp0 : p0 < 1) (hp1 : p1 < 1) :
    (∀ d0 d1 s0 s1 : ℝ, 0 < d0 → 0 < d1 → 0 < s0 → 0 < s1 →
      ((d0 = lam * (1 - p0 - γ * (d0 / s0) ^ 2) ∧ d1 = lam * (1 - p1 - γ * (d1 / s1) ^ 2) ∧
          s0 = (α * p0 - c) * (d0 / s0) ∧ s1 = (α * p1 - c) * (d1 / s1)) ↔
        (d0 = dP lam γ α c p0 ∧ d1 = dP lam γ α c p1 ∧
          s0 = sP lam γ α c p0 ∧ s1 = sP lam γ α c p1))) ∧
    (1 - p0 - γ * (dP lam γ α c p0 / sP lam γ α c p0) ^ 2 ≤
        p1 + γ * (dP lam γ α c p1 / sP lam γ α c p1) ^ 2 ↔
      dP lam γ α c p0 + dP lam γ α c p1 ≤ lam) ∧
    (∀ d0 d1 s0 s1 : ℝ, 0 < d0 → 0 < d1 → 0 < s0 → 0 < s1 →
      ((d0 = 1 / 2 * lam * (1 - p0 + p1 - γ * ((d0 / s0) ^ 2 - (d1 / s1) ^ 2)) ∧
          d1 = 1 / 2 * lam * (1 - p1 + p0 - γ * ((d1 / s1) ^ 2 - (d0 / s0) ^ 2)) ∧
          s0 = (α * p0 - c) * (d0 / s0) ∧ s1 = (α * p1 - c) * (d1 / s1)) ↔
        (d0 = dF lam γ α c p0 p1 ∧ d1 = dF lam γ α c p1 p0 ∧
          s0 = sF lam γ α c p0 p1 ∧ s1 = sF lam γ α c p1 p0))) := by sorry

end CongestedPlatforms.Surge

