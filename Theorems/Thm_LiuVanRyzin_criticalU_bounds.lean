import Mathlib
import Definitions.Def_LiuVanRyzin_PowerModel

namespace LiuVanRyzin

/-- §3.1, bounds on `v⁰` and `U_c` (Liu–van Ryzin 2008, p. 1122). `U_c` of (8) decreases in
`v⁰`; the root `v⁰` of (7) satisfies `p₁ < v⁰ < p₁ + γ(p₂ - α)`; therefore
`p₁ + γ(p₂ - α) < U_c < p₁ + p₂ - α`. -/
theorem criticalU_bounds (p₁ p₂ α γ : ℝ) (hα : α < p₂) (hp : p₂ < p₁)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    StrictAntiOn (criticalU p₁ p₂ α γ) (Set.Ioi p₁) ∧
      ∀ v₀ : ℝ, p₁ < v₀ → focLHS p₁ p₂ α γ v₀ = 0 →
        v₀ < p₁ + γ * (p₂ - α) ∧
          p₁ + γ * (p₂ - α) < criticalU p₁ p₂ α γ v₀ ∧
          criticalU p₁ p₂ α γ v₀ < p₁ + p₂ - α := by sorry

end LiuVanRyzin
