import Mathlib
import Definitions.Def_CaiCandesShen_Convergence_Shrink
import Definitions.Def_CaiCandesShen_Convergence_Problems

namespace CaiCandesShen.Convergence

open Matrix

/-- `(X, Y)` is a run of the SVT iteration (2.7), p. 1961, started from `Y⁰ = 0` (eq. (1.5),
p. 1958): for `k = 1, 2, …`, `X^k = D_τ(Y^{k−1})` and `Y^k = Y^{k−1} + δ_k P_Ω(M - X^k)`.
The index `k` of the paper is the natural number `k`; `X 0` and `δ 0` are not used. -/
def IsSVTSeq {n₁ n₂ : ℕ} (τ : ℝ) (Ω : Finset (Fin n₁ × Fin n₂)) (M : Mat n₁ n₂) (δ : ℕ → ℝ)
    (X Y : ℕ → Mat n₁ n₂) : Prop :=
  Y 0 = 0 ∧ ∀ k : ℕ, IsShrink τ (Y k) (X (k + 1)) ∧
    Y (k + 1) = Y k + δ (k + 1) • projΩ Ω (M - X (k + 1))

/-- `(X, y)` is a run of Uzawa's iteration (3.3), p. 1964, started from `y⁰ = 0`: for
`k = 1, 2, …`, `X^k = D_τ(𝒜*(y^{k−1}))` and `y^k = y^{k−1} + δ_k (b - 𝒜(X^k))`.
`X 0` and `δ 0` are not used. -/
def IsUzawaSeq {n₁ n₂ m : ℕ} (τ : ℝ) (Aop : Fin m → Mat n₁ n₂) (b : Fin m → ℝ) (δ : ℕ → ℝ)
    (X : ℕ → Mat n₁ n₂) (y : ℕ → Fin m → ℝ) : Prop :=
  y 0 = 0 ∧ ∀ k : ℕ, IsShrink τ (adjA Aop (y k)) (X (k + 1)) ∧
    y (k + 1) = y k + δ (k + 1) • (b - applyA Aop (X (k + 1)))

end CaiCandesShen.Convergence
