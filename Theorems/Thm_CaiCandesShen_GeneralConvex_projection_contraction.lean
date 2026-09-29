import Mathlib
import Definitions.Def_CaiCandesShen_GeneralConvex_Problem

namespace CaiCandesShen.GeneralConvex

/-- Proof of Theorem 4.4, p. 1969 (display after (4.5)): along a run of (3.5) with positive step
sizes and for a primal-dual optimal pair `(X⋆, y⋆)` of (3.4), for every `k ≥ 1`,
`‖y^k - y⋆‖ ≤ ‖y^{k−1} - y⋆ + δ_k (𝓕(X^k) - 𝓕(X⋆))‖`. Paper index `k` is `k + 1` here. -/
theorem projection_contraction {n₁ n₂ m : ℕ} (τ : ℝ) (hτ : 0 < τ)
    (f : Fin m → Mat n₁ n₂ → ℝ) (hconv : ∀ i, ConvexOn ℝ Set.univ (f i))
    (δ : ℕ → ℝ) (hδ : ∀ k : ℕ, 1 ≤ k → 0 < δ k)
    (X : ℕ → Mat n₁ n₂) (y : ℕ → Fin m → ℝ) (hseq : IsGeneralSVTSeq τ f δ X y)
    (Xs : Mat n₁ n₂) (ys : Fin m → ℝ) (hopt : IsPrimalDualOptimal τ f Xs ys) :
    ∀ k : ℕ, eucNorm (y (k + 1) - ys) ≤ eucNorm (y k - ys +
      δ (k + 1) • (constraintMap f (X (k + 1)) - constraintMap f Xs)) := by sorry

end CaiCandesShen.GeneralConvex
