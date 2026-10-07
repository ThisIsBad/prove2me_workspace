import Mathlib

namespace BellmanDP.GoldMining

/-- Bellman, *Dynamic Programming*, Ch. II, § 4, Eq. (4.3), and § 5, Eq. (5.1), p. 63: the
return of an A-choice (use the machine in Anaconda) at amounts `x` (Anaconda), `y` (Bonanza),
followed by the continuation `f`: `p₁ [r₁ x + f((1 − r₁) x, y)]`. -/
def goldA (p₁ r₁ : ℝ) (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  p₁ * (r₁ * x + f ((1 - r₁) * x) y)

/-- Ch. II, § 4, Eq. (4.4), and § 5, Eq. (5.1), p. 63: the return of a B-choice (use the machine
in Bonanza) followed by the continuation `f`: `p₂ [r₂ y + f(x, (1 − r₂) y)]`. -/
def goldB (p₂ r₂ : ℝ) (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  p₂ * (r₂ * y + f x ((1 - r₂) * y))

/-- Ch. II, § 5, Eq. (5.1), p. 63: `f` satisfies
`f(x, y) = Max [p₁ (r₁ x + f((1 − r₁) x, y)), p₂ (r₂ y + f(x, (1 − r₂) y))]` for all `x, y ≥ 0`. -/
def IsGoldMiningSolution (p₁ p₂ r₁ r₂ : ℝ) (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → f x y = max (goldA p₁ r₁ f x y) (goldB p₂ r₂ f x y)

/-- Ch. II, Theorem 1, p. 64: the function class of the theorem, "bounded in any rectangle
`0 ≤ x ≤ X̄, 0 ≤ y ≤ Ȳ`". -/
def BoundedOnRectangles (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ X Y : ℝ, ∃ M : ℝ, ∀ x y : ℝ, 0 ≤ x → x ≤ X → 0 ≤ y → y ≤ Y → |f x y| ≤ M

/-- Ch. II, § 4, Eqs. (4.2) and (4.5), p. 63, and § 12, Theorem 5, Eq. (1), p. 72: the `N`-stage
returns. `goldIter … 0 = 0`, so that `goldIter … 1 = Max [p₁ r₁ x, p₂ r₂ y]` is the book's `f₁`,
and `goldIter … (N + 1) = Max [A: p₁ [r₁ x + f_N((1 − r₁) x, y)], B: p₂ [r₂ y + f_N(x, (1 − r₂) y)]]`
is the book's `f_{N+1}`. -/
noncomputable def goldIter (p₁ p₂ r₁ r₂ : ℝ) : ℕ → ℝ → ℝ → ℝ
  | 0 => fun _ _ => 0
  | N + 1 => fun x y =>
      max (goldA p₁ r₁ (goldIter p₁ p₂ r₁ r₂ N) x y) (goldB p₂ r₂ (goldIter p₁ p₂ r₁ r₂ N) x y)

/-- Ch. II, § 8, p. 66 ("decision regions"): the set of points of the closed quadrant at which the
A-choice is an optimal first choice, for the value function `v` whose continuation is `f`, i.e.
where `v(x, y) = p₁ [r₁ x + f((1 − r₁) x, y)]`. For the infinite process `v = f`; for the
`(N + 1)`-stage process `v = f_{N+1}` and `f = f_N`. -/
def regionA (p₁ r₁ : ℝ) (f v : ℝ → ℝ → ℝ) : Set (ℝ × ℝ) :=
  {z | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ v z.1 z.2 = goldA p₁ r₁ f z.1 z.2}

/-- Ch. II, § 8, p. 66: the set of points of the closed quadrant at which the B-choice is an
optimal first choice, for the value function `v` whose continuation is `f`. -/
def regionB (p₂ r₂ : ℝ) (f v : ℝ → ℝ → ℝ) : Set (ℝ × ℝ) :=
  {z | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ v z.1 z.2 = goldB p₂ r₂ f z.1 z.2}

/-- Ch. II, § 14, Theorem 7, Eq. (2), p. 76: `g` satisfies the perturbed equation
`g(x, y) = Max [A: p₁ [r₁ x + g((1 − r₁) x, y)], B: p₂ [r₂ y + g(x, (1 − r₂) y)]] + h(x, y)`
for all `x, y ≥ 0`. -/
def IsPerturbedSolution (p₁ p₂ r₁ r₂ : ℝ) (h g : ℝ → ℝ → ℝ) : Prop :=
  ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → g x y = max (goldA p₁ r₁ g x y) (goldB p₂ r₂ g x y) + h x y

end BellmanDP.GoldMining
