import Mathlib

namespace BellmanDP.Fibonacci

/-- Bellman, *Dynamic Programming*, Ch. I, § 22, Theorem 11, p. 34: the book's Fibonacci
sequence, with `F₀ = F₁ = 1` and `F_n = F_{n−1} + F_{n−2}` for `n ≥ 2`.
(In Mathlib's indexing this is `Nat.fib (n + 1)`.) -/
def bookFib : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | (n + 2) => bookFib (n + 1) + bookFib n

/-- A deterministic, adaptive search procedure, as a decision tree. At a `query x next` node the
procedure calculates the value `f x` of the unknown function and continues with the subtree
`next (f x)`; at a `stop b` node it stops and announces `b`. Along any path, the point queried at
each step is determined by the values observed at the earlier steps, and by nothing else about
`f`. `α` is the type of points that may be queried, `β` the type of announcements. -/
inductive SearchTree (α β : Type) : Type where
  | stop : β → SearchTree α β
  | query : α → (ℝ → SearchTree α β) → SearchTree α β

namespace SearchTree

variable {α β : Type}

/-- The announcement of the procedure `T` when run against the function `f`. -/
def result : SearchTree α β → (α → ℝ) → β
  | stop b, _ => b
  | query x next, f => result (next (f x)) f

/-- The number of values of `f` the procedure `T` calculates when run against `f`. -/
def cost : SearchTree α β → (α → ℝ) → ℕ
  | stop _, _ => 0
  | query x next, f => cost (next (f x)) f + 1

end SearchTree

/-- Ch. I, § 22, p. 34: `f` is *strictly unimodal on `[0, L]` with maximum at `m`*: `m ∈ [0, L]`,
`f` is strictly increasing on `[0, m]` and strictly decreasing on `[m, L]`. No continuity is
assumed; the endpoint cases `m = 0` and `m = L` are allowed. `m` is then the unique maximizer of
`f` on `[0, L]` (its single relative maximum). -/
def IsStrictUnimodalOn (f : ℝ → ℝ) (L m : ℝ) : Prop :=
  m ∈ Set.Icc 0 L ∧ StrictMonoOn f (Set.Icc 0 m) ∧ StrictAntiOn f (Set.Icc m L)

/-- The procedure `T` (announcing a closed interval `[a, b]` as the pair `(a, b)`) *always locates
the maximum of a strictly unimodal function on `[0, L]` within length `δ` by calculating at most
`n` values*: for every `f` strictly unimodal on `[0, L]` with maximum at `m`, `T` calculates at
most `n` values of `f`, and the interval `[a, b]` it announces satisfies `a ≤ b`, `b − a ≤ δ` and
`m ∈ [a, b]`. -/
def Locates (T : SearchTree ℝ (ℝ × ℝ)) (L δ : ℝ) (n : ℕ) : Prop :=
  ∀ (f : ℝ → ℝ) (m : ℝ), IsStrictUnimodalOn f L m →
    T.cost f ≤ n ∧
    (T.result f).1 ≤ (T.result f).2 ∧
    (T.result f).2 - (T.result f).1 ≤ δ ∧
    m ∈ Set.Icc (T.result f).1 (T.result f).2

/-- Ch. I, § 22, p. 34: the set of interval lengths `L_n > 0` such that the maximum of every
strictly unimodal function on `[0, L_n]` can always be located on a sub-interval of unit length
by calculating at most `n` values of the function. Bellman's `F_n = Sup L_n` (Eq. (22.1)) is the
least upper bound of this set. -/
def feasibleLengths (n : ℕ) : Set ℝ :=
  {L : ℝ | 0 < L ∧ ∃ T : SearchTree ℝ (ℝ × ℝ), Locates T L 1 n}

/-- Ch. I, § 22, p. 36 (discrete version): `f` is *strictly unimodal on the points
`0, 1, …, N − 1` with maximum at `m`*: `m < N`, `f` is strictly increasing on `{0, …, m}` and
strictly decreasing on `{m, …, N − 1}`. -/
def IsStrictUnimodalOnPoints (f : ℕ → ℝ) (N m : ℕ) : Prop :=
  m < N ∧ StrictMonoOn f (Set.Iic m) ∧ StrictAntiOn f (Set.Ico m N)

/-- Ch. I, § 22, p. 36: the set of numbers `N ≥ 1` of points such that the maximum of every
strictly unimodal function on the points `0, …, N − 1` can always be identified in `n`
computations: some procedure querying points (natural numbers) calculates at most `n` values
and announces exactly the maximizer `m`. Bellman's `K_n` is the greatest element of this set. -/
def identifiableSizes (n : ℕ) : Set ℕ :=
  {N : ℕ | 1 ≤ N ∧ ∃ T : SearchTree ℕ ℕ, ∀ (f : ℕ → ℝ) (m : ℕ),
    IsStrictUnimodalOnPoints f N m → T.cost f ≤ n ∧ T.result f = m}

end BellmanDP.Fibonacci
