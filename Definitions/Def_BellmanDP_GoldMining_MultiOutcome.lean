import Mathlib

namespace BellmanDP.GoldMining

/-- Bellman, *Dynamic Programming*, Ch. II, § 10, Theorem 3, Eq. (1), p. 69, choice A: with `K`
possible outcomes `k`, outcome `k` occurring with probability `p k`, yielding the fraction `c k`
of the gold `x` and leaving `c' k * x`:
`Σ_k p_k [c_k x + f(c'_k x, y)]`. -/
def optA (K : ℕ) (p c c' : Fin K → ℝ) (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  ∑ k : Fin K, p k * (c k * x + f (c' k * x) y)

/-- Ch. II, Theorem 3, Eq. (1), p. 69, choice B: `Σ_k q_k [d_k y + f(x, d'_k y)]`. -/
def optB (K : ℕ) (q d d' : Fin K → ℝ) (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  ∑ k : Fin K, q k * (d k * y + f x (d' k * y))

/-- Ch. II, Theorem 3, Eq. (1), p. 69: `f(x, y) = Max [A, B]` for all `x, y ≥ 0`. -/
def IsTwoMineSolution (K : ℕ) (p c c' q d d' : Fin K → ℝ) (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → f x y = max (optA K p c c' f x y) (optB K q d d' f x y)

/-- Ch. II, Theorem 4, Eq. (4), p. 70: the `i`-th alternative of the `n`-mine equation at the state
`x = (x_1, …, x_n)`, `Σ_k p_ik [c_ik x_i + f(x_1, …, c'_ik x_i, …, x_n)]`, where only the `i`-th
coordinate is replaced (by `c'_ik x_i`). -/
def mineOption {n K : ℕ} (p c c' : Fin n → Fin K → ℝ) (f : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ k : Fin K, p i k * (c i k * x i + f (Function.update x i (c' i k * x i)))

/-- Ch. II, Theorem 4, Eq. (4), p. 70: `f(x) = Max_i mineOption i` for every `x` with all
`x_i ≥ 0`: every alternative is at most `f(x)` and some alternative equals `f(x)`. -/
def IsNMineSolution {n K : ℕ} (p c c' : Fin n → Fin K → ℝ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ x : Fin n → ℝ, (∀ i, 0 ≤ x i) →
    (∀ i, mineOption p c c' f x i ≤ f x) ∧ ∃ i, f x = mineOption p c c' f x i

/-- The function class for the `n`-mine equation: bounded on every box
`0 ≤ x_i ≤ X̄_i, i = 1, …, n` (the `n`-dimensional form of Ch. II, Theorem 1's class). -/
def BoundedOnBoxes {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ X : Fin n → ℝ, ∃ M : ℝ, ∀ x : Fin n → ℝ, (∀ i, 0 ≤ x i ∧ x i ≤ X i) → |f x| ≤ M

/-- Ch. II, Theorem 4, p. 70: the decision function
`D_i(x) = (Σ_k p_ik c_ik) x_i / (1 − Σ_k p_ik)`. -/
noncomputable def decisionFunction {n K : ℕ} (p c : Fin n → Fin K → ℝ) (x : Fin n → ℝ)
    (i : Fin n) : ℝ :=
  (∑ k : Fin K, p i k * c i k) * x i / (1 - ∑ k : Fin K, p i k)

end BellmanDP.GoldMining
