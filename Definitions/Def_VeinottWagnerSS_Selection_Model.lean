import Mathlib

namespace VeinottWagnerSS.Selection

open scoped ENNReal

/-- The reduced periodic-review inventory model of Veinott & Wagner (1965), pp. 526–529, with its
standing assumptions. By Eq. (2), p. 529, the model depends on the original data (unit cost `c`,
holding and penalty cost `L`, lead time `λ`) only through the one-period function `G = G_α`, so
`G` is a primitive here, for the fixed discount factor `α` at hand.

* `φ` is the probability distribution of the i.i.d. one-period demands `ξ₁, ξ₂, ⋯`, which are
  non-negative integers (p. 526); its mean `μ = E(ξ)` is finite (p. 528).
* `K ≥ 0` is the set-up cost of an order (p. 527).
* `G : ℤ → ℝ` is `G_α` (p. 527): convex (as `(1 − α)cy + L(y)` with `L` convex, `c ≥ 0`),
  written on the integers as non-decreasing forward differences, and `G(y) → ∞` as `|y| → ∞`. -/
structure Model where
  /-- The demand distribution, `φ k = Pr(ξ_t = k)`. -/
  φ : PMF ℕ
  /-- `μ = E(ξ) < ∞` (p. 528). -/
  mean_finite : ∑' k : ℕ, (k : ℝ≥0∞) * φ k ≠ ⊤
  /-- The set-up cost `K`. -/
  K : ℝ
  K_nonneg : 0 ≤ K
  /-- The conditional expected holding and penalty cost `G_α`. -/
  G : ℤ → ℝ
  /-- Discrete convexity of `G_α`: `ΔG(y) ≤ ΔG(y + 1)`. -/
  G_convex : ∀ y : ℤ, G (y + 1) - G y ≤ G (y + 2) - G (y + 1)
  /-- `G_α(y) → ∞` as `y → +∞`. -/
  G_tendsto_atTop : Filter.Tendsto G Filter.atTop Filter.atTop
  /-- `G_α(y) → ∞` as `y → −∞`. -/
  G_tendsto_atBot : Filter.Tendsto G Filter.atBot Filter.atTop

/-- `δ(z)` of p. 527: `δ(0) = 0` and `δ(z) = 1` for `z > 0` (orders are non-negative; the value
`0` is also returned for `z < 0`, which never occurs below since `Y_t ≥ X_t`). -/
def delta (z : ℤ) : ℝ := if 0 < z then 1 else 0

/-- The stationary `(s, S)` ordering rule (p. 529): `Y = S` if `X < s`, and `Y = X` if `X ≥ s`. -/
def sSOrder (s S x : ℤ) : ℤ := if x < s then S else x

/-- The law of the stock level before ordering when the stationary `(s, S)` policy is followed
from `X₁ = x`: `stateLaw M s S x t` is the distribution of `X_{t+1}`. `X₁ = x` surely, and
`X_{t+1} = Y_t − ξ_t` (p. 527) with `Y_t = sSOrder s S X_t` and the demand `ξ_t`, of law `φ`,
independent of `X_t`. -/
noncomputable def stateLaw (M : Model) (s S x : ℤ) : ℕ → PMF ℤ
  | 0 => PMF.pure x
  | t + 1 => (stateLaw M s S x t).bind
      (fun y => M.φ.map (fun k : ℕ => sSOrder s S y - (k : ℤ)))

/-- The cost of a period that starts with stock `y` under the `(s, S)` rule, in the reduced
model (2), p. 529: `K δ(Y − X) + G_α(Y)` with `X = y` and `Y = sSOrder s S y`. -/
noncomputable def periodCost (M : Model) (s S y : ℤ) : ℝ :=
  M.K * delta (sSOrder s S y - y) + M.G (sSOrder s S y)

/-- The expected cost of period `t + 1`, `E[K δ(Y_{t+1} − X_{t+1}) + G_α(Y_{t+1})]`, under the
stationary `(s, S)` policy from `X₁ = x`. Along the chain every `Y_{t+1}` lies in the finite
interval `[s, max(x, S)]` (for `s ≤ S`), so the sum is absolutely convergent. -/
noncomputable def expectedPeriodCost (M : Model) (s S x : ℤ) (t : ℕ) : ℝ :=
  ∑' y : ℤ, (stateLaw M s S x t y).toReal * periodCost M s S y

/-- `f(x | s, S)` (p. 533, with (2)–(3) of p. 529): the total expected cost of the stationary
`(s, S)` policy from `X₁ = x`, discounted to the beginning of the first period,
`f(x | s, S) = ∑_{t=1}^{∞} α^{t−1} E[K δ(Y_t − X_t) + G_α(Y_t)]`
(the summand of index `t` below is period `t + 1`, discounted by `α^t`). -/
noncomputable def fCost (M : Model) (α : ℝ) (s S x : ℤ) : ℝ :=
  ∑' t : ℕ, α ^ t * expectedPeriodCost M s S x t

/-- The equivalent average cost per period `a_α(x | s, S) = (1 − α) f(x | s, S)` (p. 534). -/
noncomputable def aCost (M : Model) (α : ℝ) (s S x : ℤ) : ℝ :=
  (1 - α) * fCost M α s S x

/-- Accessibility (p. 542): under the `(s, S)` policy, `x'` is accessible from `X₁ = x` if there
is a `t > 1` with `Pr(X_t = x' | X₁ = x) > 0`. Here `stateLaw M s S x t'` is the law of
`X_{t'+1}`, so `t = t' + 1 > 1` is `t' ≥ 1`. -/
def Accessible (M : Model) (s S x x' : ℤ) : Prop :=
  ∃ t : ℕ, 1 ≤ t ∧ stateLaw M s S x t x' ≠ 0

/-- Optimality for a set of starting stocks (p. 536): `(s', S')` (an `(s, S)` policy, so
`s' ≤ S'`) is optimal for the set of integers `X` if for each `x ∈ X` it minimizes
`a_α(x | s, S)` over the class of all `(s, S)` policies (`s ≤ S`). -/
def OptimalFor (M : Model) (α : ℝ) (X : Set ℤ) (s' S' : ℤ) : Prop :=
  s' ≤ S' ∧ ∀ x ∈ X, ∀ s S : ℤ, s ≤ S → aCost M α s' S' x ≤ aCost M α s S x

/-- An optimal `(s, S)` policy (p. 536): optimal for every integer starting stock `x`. -/
def Optimal (M : Model) (α : ℝ) (s' S' : ℤ) : Prop :=
  OptimalFor M α Set.univ s' S'

end VeinottWagnerSS.Selection
