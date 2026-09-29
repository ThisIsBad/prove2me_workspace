import Mathlib
import Definitions.Def_CaiCandesShen_GeneralConvex_Problem

namespace CaiCandesShen.GeneralConvex

/-- Eq. (4.6), proof of Theorem 4.4, p. 1970: let `𝓕` obey the Lipschitz bound (4.2) with
constant `L ≥ 0`, and let `β > 0` with `2δ_k - δ_k² L² ≥ β` for all `k ≥ 1`. Along a run of (3.5)
and for a primal-dual optimal pair `(X⋆, y⋆)` of (3.4), for every `k ≥ 1`,
`‖y^k - y⋆‖² ≤ ‖y^{k−1} - y⋆‖² - β ‖X^k - X⋆‖_F²`. Paper index `k` is `k + 1` here. -/
theorem fejer_inequality {n₁ n₂ m : ℕ} (τ : ℝ) (hτ : 0 < τ)
    (f : Fin m → Mat n₁ n₂ → ℝ) (hconv : ∀ i, ConvexOn ℝ Set.univ (f i))
    (L : ℝ) (hL0 : 0 ≤ L)
    (hL : ∀ X Y : Mat n₁ n₂, eucNorm (constraintMap f X - constraintMap f Y) ≤ L * frobNorm (X - Y))
    (δ : ℕ → ℝ) (β : ℝ) (hβ : 0 < β) (hδβ : ∀ k : ℕ, 1 ≤ k → β ≤ 2 * δ k - δ k ^ 2 * L ^ 2)
    (X : ℕ → Mat n₁ n₂) (y : ℕ → Fin m → ℝ) (hseq : IsGeneralSVTSeq τ f δ X y)
    (Xs : Mat n₁ n₂) (ys : Fin m → ℝ) (hopt : IsPrimalDualOptimal τ f Xs ys) :
    ∀ k : ℕ, eucNorm (y (k + 1) - ys) ^ 2 ≤
      eucNorm (y k - ys) ^ 2 - β * frobNorm (X (k + 1) - Xs) ^ 2 := by sorry

end CaiCandesShen.GeneralConvex
