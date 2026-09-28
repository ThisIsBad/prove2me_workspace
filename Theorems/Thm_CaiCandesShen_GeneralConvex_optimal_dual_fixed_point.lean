import Mathlib
import Definitions.Def_CaiCandesShen_GeneralConvex_Problem

namespace CaiCandesShen.GeneralConvex

/-- Lemma 4.3, p. 1969: if `(X⋆, y⋆)` is a primal-dual optimal pair for (3.4), then for each
`δ > 0`, `y⋆ = [y⋆ + δ 𝓕(X⋆)]_+` (eq. (4.3)), the positive part taken entrywise. -/
theorem optimal_dual_fixed_point {n₁ n₂ m : ℕ} (τ : ℝ) (hτ : 0 < τ)
    (f : Fin m → Mat n₁ n₂ → ℝ) (hconv : ∀ i, ConvexOn ℝ Set.univ (f i))
    (Xs : Mat n₁ n₂) (ys : Fin m → ℝ) (hopt : IsPrimalDualOptimal τ f Xs ys)
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ i : Fin m, ys i = max (ys i + δ * constraintMap f Xs i) 0 := by sorry

end CaiCandesShen.GeneralConvex
