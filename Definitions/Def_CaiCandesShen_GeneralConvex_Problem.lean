import Mathlib
import Definitions.Def_CaiCandesShen_GeneralConvex_Basic

namespace CaiCandesShen.GeneralConvex

/-- The constraint map `𝓕(X) = (f_1(X), …, f_m(X))` (§3.2, p. 1965). -/
def constraintMap {n₁ n₂ m : ℕ} (f : Fin m → Mat n₁ n₂ → ℝ) (X : Mat n₁ n₂) : Fin m → ℝ :=
  fun i => f i X

/-- The Lagrangian `𝓛(X, y) = f_τ(X) + ⟨y, 𝓕(X)⟩` of problem (3.4) (§3.2, p. 1965). -/
noncomputable def lagr {n₁ n₂ m : ℕ} (τ : ℝ) (f : Fin m → Mat n₁ n₂ → ℝ) (X : Mat n₁ n₂)
    (y : Fin m → ℝ) : ℝ :=
  fτ τ X + dot y (constraintMap f X)

/-- `Xs` solves problem (3.4), p. 1965: it is feasible, `f_i(Xs) ≤ 0` for all `i`, and
`f_τ(Xs) ≤ f_τ(X)` for every feasible `X`. -/
def IsSol34 {n₁ n₂ m : ℕ} (τ : ℝ) (f : Fin m → Mat n₁ n₂ → ℝ) (Xs : Mat n₁ n₂) : Prop :=
  (∀ i, f i Xs ≤ 0) ∧ ∀ X : Mat n₁ n₂, (∀ i, f i X ≤ 0) → fτ τ Xs ≤ fτ τ X

/-- `(Xs, ys)` is a primal-dual optimal pair of (3.4) in the saddle-point sense of (2.11),
p. 1963: `ys ≥ 0`, `𝓛(Xs, y) ≤ 𝓛(Xs, ys)` for every `y ≥ 0`, and `𝓛(Xs, ys) ≤ 𝓛(X, ys)` for
every `X`. -/
def IsPrimalDualOptimal {n₁ n₂ m : ℕ} (τ : ℝ) (f : Fin m → Mat n₁ n₂ → ℝ) (Xs : Mat n₁ n₂)
    (ys : Fin m → ℝ) : Prop :=
  (∀ i, 0 ≤ ys i) ∧
    (∀ y : Fin m → ℝ, (∀ i, 0 ≤ y i) → lagr τ f Xs y ≤ lagr τ f Xs ys) ∧
    ∀ X : Mat n₁ n₂, lagr τ f Xs ys ≤ lagr τ f X ys

/-- `(X, y)` is a run of the iteration (3.5), p. 1965, started from `y⁰ = 0` (as in (3.3),
p. 1964): for `k = 1, 2, …`, `X^k` minimizes `𝓛(·, y^{k−1})` and
`y^k = [y^{k−1} + δ_k 𝓕(X^k)]_+`, the positive part taken entrywise. The index `k` of the
paper is the natural number `k`; `X 0` and `δ 0` are not used. -/
def IsGeneralSVTSeq {n₁ n₂ m : ℕ} (τ : ℝ) (f : Fin m → Mat n₁ n₂ → ℝ) (δ : ℕ → ℝ)
    (X : ℕ → Mat n₁ n₂) (y : ℕ → Fin m → ℝ) : Prop :=
  y 0 = 0 ∧
    (∀ k : ℕ, ∀ X' : Mat n₁ n₂, lagr τ f (X (k + 1)) (y k) ≤ lagr τ f X' (y k)) ∧
    ∀ k : ℕ, ∀ i : Fin m,
      y (k + 1) i = max (y k i + δ (k + 1) * constraintMap f (X (k + 1)) i) 0

end CaiCandesShen.GeneralConvex
