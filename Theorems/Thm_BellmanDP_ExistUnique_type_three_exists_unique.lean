import Mathlib
import Definitions.Def_BellmanDP_ExistUnique_TypeThree

namespace BellmanDP.ExistUnique

/-- Bellman, *Dynamic Programming*, Ch. IV, § 8, Theorem 5, p. 126. If for each transformation
`T_l` and all `p`, `Σ_{k=1}^n p_{kl} ≤ c₁` with `0 < c₁ < 1`, then equation (8.1) has a unique
bounded solution on the simplex, and this solution is positive for `p ≠ x₀`. -/
theorem type_three_exists_unique (n M : ℕ)
    (Tr : Fin M → (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)) (c₁ : ℝ)
    (hT : TypeThreeHyp n M Tr c₁) :
    ∃ f : (Fin (n + 1) → ℝ) → ℝ,
      (BoundedOnSimplex n f ∧ SolvesTypeThree n M Tr f) ∧
      (∀ g : (Fin (n + 1) → ℝ) → ℝ, BoundedOnSimplex n g → SolvesTypeThree n M Tr g →
        ∀ p ∈ simplex n, g p = f p) ∧
      (∀ p ∈ simplex n, p ≠ vertex n 0 → 0 < f p) := by sorry

end BellmanDP.ExistUnique

