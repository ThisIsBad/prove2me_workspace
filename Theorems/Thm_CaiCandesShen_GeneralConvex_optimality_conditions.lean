import Mathlib
import Definitions.Def_CaiCandesShen_GeneralConvex_Problem

namespace CaiCandesShen.GeneralConvex

/-- Eq. (4.4), proof of Theorem 4.4, p. 1969: along a run `(X^k, y^k)` of (3.5) and for a
primal-dual optimal pair `(X⋆, y⋆)` of (3.4), for every `k ≥ 1` there is `Z^k ∈ ∂f_τ(X^k)` with
`⟨Z^k, X - X^k⟩ + ⟨y^{k−1}, 𝓕(X) - 𝓕(X^k)⟩ ≥ 0` for all `X`, and there is `Z⋆ ∈ ∂f_τ(X⋆)` with
`⟨Z⋆, X - X⋆⟩ + ⟨y⋆, 𝓕(X) - 𝓕(X⋆)⟩ ≥ 0` for all `X`. Paper index `k` is `k + 1` here. -/
theorem optimality_conditions {n₁ n₂ m : ℕ} (τ : ℝ) (hτ : 0 < τ)
    (f : Fin m → Mat n₁ n₂ → ℝ) (hconv : ∀ i, ConvexOn ℝ Set.univ (f i))
    (δ : ℕ → ℝ) (X : ℕ → Mat n₁ n₂) (y : ℕ → Fin m → ℝ) (hseq : IsGeneralSVTSeq τ f δ X y)
    (Xs : Mat n₁ n₂) (ys : Fin m → ℝ) (hopt : IsPrimalDualOptimal τ f Xs ys) :
    (∀ k : ℕ, ∃ Z : Mat n₁ n₂, IsSubgradient (fτ τ) (X (k + 1)) Z ∧
        ∀ X' : Mat n₁ n₂, 0 ≤ frobInner Z (X' - X (k + 1)) +
          dot (y k) (constraintMap f X' - constraintMap f (X (k + 1)))) ∧
      ∃ Zs : Mat n₁ n₂, IsSubgradient (fτ τ) Xs Zs ∧
        ∀ X' : Mat n₁ n₂, 0 ≤ frobInner Zs (X' - Xs) +
          dot ys (constraintMap f X' - constraintMap f Xs) := by sorry

end CaiCandesShen.GeneralConvex
