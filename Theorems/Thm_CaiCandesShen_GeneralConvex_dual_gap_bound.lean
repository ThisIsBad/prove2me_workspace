import Mathlib
import Definitions.Def_CaiCandesShen_GeneralConvex_Problem

namespace CaiCandesShen.GeneralConvex

/-- Eq. (4.5), proof of Theorem 4.4, p. 1969 (outer inequality): along a run of (3.5) and for a
primal-dual optimal pair `(X⋆, y⋆)` of (3.4), for every `k ≥ 1`,
`⟨y^{k−1} - y⋆, 𝓕(X^k) - 𝓕(X⋆)⟩ ≤ -‖X^k - X⋆‖_F²`. Paper index `k` is `k + 1` here. -/
theorem dual_gap_bound {n₁ n₂ m : ℕ} (τ : ℝ) (hτ : 0 < τ)
    (f : Fin m → Mat n₁ n₂ → ℝ) (hconv : ∀ i, ConvexOn ℝ Set.univ (f i))
    (δ : ℕ → ℝ) (X : ℕ → Mat n₁ n₂) (y : ℕ → Fin m → ℝ) (hseq : IsGeneralSVTSeq τ f δ X y)
    (Xs : Mat n₁ n₂) (ys : Fin m → ℝ) (hopt : IsPrimalDualOptimal τ f Xs ys) :
    ∀ k : ℕ, dot (y k - ys) (constraintMap f (X (k + 1)) - constraintMap f Xs) ≤
      -(frobNorm (X (k + 1) - Xs) ^ 2) := by sorry

end CaiCandesShen.GeneralConvex
