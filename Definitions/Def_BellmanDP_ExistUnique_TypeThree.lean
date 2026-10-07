import Mathlib

namespace BellmanDP.ExistUnique

/-- Bellman, *Dynamic Programming*, Ch. IV, § 8, Eq. (8.2), p. 125: the probability simplex
`p = (p₀, …, pₙ)`, `pᵢ ≥ 0`, `Σ_{i=0}^n pᵢ = 1`. -/
def simplex (n : ℕ) : Set (Fin (n + 1) → ℝ) :=
  {p | (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1}

/-- Eq. (8.2): the vertex `x_k = (0, …, 1, …, 0)`, the `1` in the `k`-th place. -/
def vertex (n : ℕ) (k : Fin (n + 1)) : Fin (n + 1) → ℝ :=
  Pi.single k 1

/-- Ch. IV, § 8, Eq. (8.2) and Theorem 5, condition (3), p. 126: the transformations
`T_l p = (p_{0l}, …, p_{nl})`, `l = 1, …, M` (indexed here by `Fin M`), map the simplex into
itself with `p_{0l} ≠ 1`, and `Σ_{k=1}^n p_{kl} ≤ c₁` with `0 < c₁ < 1`, for all `p`. -/
structure TypeThreeHyp (n M : ℕ) (Tr : Fin M → (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ))
    (c₁ : ℝ) : Prop where
  /-- `l` runs over `1, 2, …, M`, so there is at least one transformation. -/
  M_pos : 0 < M
  /-- (8.2) `p_{il} ≥ 0`, `Σ_{i=0}^n p_{il} = 1`. -/
  mapsTo : ∀ l, ∀ p ∈ simplex n, Tr l p ∈ simplex n
  /-- (8.2) `p_{0l} ≠ 1`. -/
  zero_ne_one : ∀ l, ∀ p ∈ simplex n, Tr l p 0 ≠ 1
  /-- Theorem 5 (3): `0 < c₁`. -/
  c_pos : 0 < c₁
  /-- Theorem 5 (3): `c₁ < 1`. -/
  c_lt_one : c₁ < 1
  /-- Theorem 5 (3): `Σ_{k=1}^n p_{kl} ≤ c₁`. -/
  tail_le : ∀ l, ∀ p ∈ simplex n, ∑ k : Fin n, Tr l p k.succ ≤ c₁

/-- Ch. IV, § 8, Eq. (8.1), p. 125: `f` solves
`f(p) = Min [1 + Σ_{k=0}^n p_k f(x_k), Min_l [1 + f(T_l p)]]` for `p ≠ x₀` in the simplex, and
`f(x₀) = 0`. (`Min_l` is a finite infimum over `Fin M`, genuine when `0 < M`.) -/
def SolvesTypeThree (n M : ℕ) (Tr : Fin M → (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ))
    (f : (Fin (n + 1) → ℝ) → ℝ) : Prop :=
  f (vertex n 0) = 0 ∧
    ∀ p ∈ simplex n, p ≠ vertex n 0 →
      f p = min (1 + ∑ k, p k * f (vertex n k)) (⨅ l : Fin M, (1 + f (Tr l p)))

/-- A bounded function on the simplex. -/
def BoundedOnSimplex (n : ℕ) (f : (Fin (n + 1) → ℝ) → ℝ) : Prop :=
  ∃ B : ℝ, ∀ p ∈ simplex n, |f p| ≤ B

end BellmanDP.ExistUnique
