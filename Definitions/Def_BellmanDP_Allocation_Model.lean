import Mathlib

namespace BellmanDP.Allocation

/-- Bellman, *Dynamic Programming*, Ch. I, § 9, Eq. (9.3), p. 12: the one-stage return
`T(f, y) = g(y) + h(x − y) + f(ay + b(x − y))` of allocating `y` of the quantity `x` to the
first activity and `x − y` to the second, followed by the total return `f` of what is left. -/
def allocT (g h : ℝ → ℝ) (a b : ℝ) (f : ℝ → ℝ) (x y : ℝ) : ℝ :=
  g y + h (x - y) + f (a * y + b * (x - y))

/-- Ch. I, Theorem 1, hypothesis (1b), p. 12: `m(x) = Max_{0 ≤ y ≤ x} Max(|g(y)|, |h(y)|)`.
For `g, h` continuous on `[0, ∞)` and `x ≥ 0` the supremum is over a compact interval and is
attained, so it is the book's maximum. -/
noncomputable def allocM (g h : ℝ → ℝ) (x : ℝ) : ℝ :=
  sSup ((fun y => max |g y| |h y|) '' Set.Icc 0 x)

/-- Ch. I, Theorem 1, hypotheses (1a)–(1c), p. 12. -/
structure AllocationHyp (g h : ℝ → ℝ) (a b : ℝ) : Prop where
  /-- (1a) `g` is continuous for `x ≥ 0`. -/
  cont_g : ContinuousOn g (Set.Ici 0)
  /-- (1a) `h` is continuous for `x ≥ 0`. -/
  cont_h : ContinuousOn h (Set.Ici 0)
  /-- (1a) `g(0) = 0`. -/
  g_zero : g 0 = 0
  /-- (1a) `h(0) = 0`. -/
  h_zero : h 0 = 0
  /-- (1b) with `c = Max(a, b)`: `Σ_{n=0}^∞ m(cⁿ x) < ∞` for all `x ≥ 0`. -/
  summable_m : ∀ x : ℝ, 0 ≤ x → Summable (fun n : ℕ => allocM g h (max a b ^ n * x))
  /-- (1c) `0 ≤ a`. -/
  a_nonneg : 0 ≤ a
  /-- (1c) `a < 1`. -/
  a_lt_one : a < 1
  /-- (1c) `0 ≤ b`. -/
  b_nonneg : 0 ≤ b
  /-- (1c) `b < 1`. -/
  b_lt_one : b < 1

/-- Ch. I, § 8, Eq. (8.1), p. 11: `f` solves `f(x) = Max_{0 ≤ y ≤ x} T(f, y)` for every
`x ≥ 0`, the maximum being attained (`IsGreatest`). -/
def IsAllocationSolution (g h : ℝ → ℝ) (a b : ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, 0 ≤ x → IsGreatest ((fun y => allocT g h a b f x y) '' Set.Icc 0 x) (f x)

/-- Ch. I, § 9, Eq. (9.4), p. 12, and § 10, Eq. (10.2), p. 16: the successive approximations
`f_{N+1}(x) = Max_{0 ≤ y ≤ x} T(f_N, y)` started from `f₀`. -/
noncomputable def allocIter (g h : ℝ → ℝ) (a b : ℝ) (f₀ : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => f₀
  | N + 1 => fun x => sSup ((fun y => allocT g h a b (allocIter g h a b f₀ N) x y) '' Set.Icc 0 x)

end BellmanDP.Allocation
