import Mathlib
import Definitions.Def_TheoryOfGames_Utility_UtilitySystem

namespace TheoryOfGames.Utility

/-- (A:R) and (A:S): for fixed `u* < v*` there is a mapping `h` of all utilities to numbers
with (i) `h(u*) = 0`, (ii) `h(v*) = 1`, (iii) `h` monotone, (iv) for `0 < γ < 1` and `u < v`,
`h((1 − γ)u + γv) = (1 − γ)h(u) + γh(v)`; and every mapping of all utilities to numbers with
(i), (ii) and (iv) is identical with `h`. -/
theorem normalized_utility_exists_unique {U : Type*} (S : UtilitySystem U) {uStar vStar : U}
    (hStar : S.lt uStar vStar) :
    ∃ h : U → ℝ,
      (h uStar = 0 ∧ h vStar = 1 ∧ (∀ u v : U, S.lt u v → h u < h v) ∧
        ∀ (γ : OpenUnit) (u v : U), S.lt u v →
          h (S.cmb γ u v) = (1 - (γ : ℝ)) * h u + (γ : ℝ) * h v) ∧
      ∀ h₁ : U → ℝ, h₁ uStar = 0 → h₁ vStar = 1 →
        (∀ (γ : OpenUnit) (u v : U), S.lt u v →
          h₁ (S.cmb γ u v) = (1 - (γ : ℝ)) * h₁ u + (γ : ℝ) * h₁ v) →
        h₁ = h := by sorry

end TheoryOfGames.Utility

