import Mathlib

open scoped ENNReal NNReal

namespace ServiceParts.UnitDecomp

/-- The data of the single-item, single-location periodic-review system of Section 2.2.1
(Muckstadt, pp. 23–25), with the standing assumptions of the section as fields.

* `σ` is the finite state space of the exogenous Markov chain `sₙ`; `trans s` is the law of
  `sₙ₊₁` given `sₙ = s` (time-homogeneous), `demand s` the law of the period demand `Dₙ` given
  `sₙ = s`. `Dₙ` and `sₙ₊₁` are conditionally independent given `sₙ`.
* Units live at locations `0, 1, …, m + 1` (`0` used, `1` on hand, `2, …, m` in transit,
  `m + 1` at the supplier); an order placed in period `n` is on hand in period `n + m − 1`.
* `h` is the holding cost per unit on hand and `b` the backorder cost per waiting customer,
  charged at the end of each period; `α` is the discount factor (`α = 1`: undiscounted). -/
structure Model (σ : Type) [Fintype σ] where
  /-- transition law of the exogenous Markov chain -/
  trans : σ → PMF σ
  /-- law of the period demand given the current Markov state -/
  demand : σ → PMF ℕ
  /-- the supplier location is `m + 1`; the lead time is `m − 1` periods -/
  m : ℕ
  /-- holding cost per unit on hand at the end of a period -/
  h : ℝ≥0
  /-- backorder cost per waiting customer at the end of a period -/
  b : ℝ≥0
  /-- discount factor -/
  α : ℝ≥0
  one_le_m : 1 ≤ m
  h_pos : 0 < h
  h_lt_b : h < b
  α_pos : 0 < α
  α_le_one : α ≤ 1

/-- The two decisions available for a unit at the supplier (location `m + 1`). -/
inductive Decision
  | release
  | hold
  deriving DecidableEq

/-- Event 2 of the period for one unit: a unit at a location `2, …, m` moves one location
closer; a unit at the supplier location `m + 1` that is released moves to location `m`;
every other unit stays where it is. -/
def unitMove (m z : ℕ) (rel : Bool) : ℕ :=
  if 2 ≤ z ∧ z ≤ m then z - 1 else if z = m + 1 ∧ rel = true then m else z

/-- Event 3 of the period for one customer when the period demand is `d`: a customer at
distance `2, …, d + 1` arrives (distance `1`), a customer at distance `y ≥ d + 2` moves to
distance `y − d`, and customers at distance `0` (served) or `1` (waiting) stay. -/
def custMove (d y : ℕ) : ℕ :=
  if 2 ≤ y then (if y ≤ d + 1 then 1 else y - d) else y

variable {σ : Type} [Fintype σ]

/-- Expected (discounted) cost of a Markov policy `π` over `k` periods, starting in period `n`
with Markov state `s` and physical configuration `x`. In each period the policy picks an
action from `(n, s, x)`, the demand `d` is drawn from `demand s`, the configuration moves to
`post x a d` and the end-of-period cost `stage (post x a d)` is charged; the next Markov
state is drawn from `trans s`, and later periods are discounted by `α`. -/
noncomputable def Model.costToGo {X A : Type} (M : Model σ) (post : X → A → ℕ → X)
    (stage : X → ℝ≥0∞) (π : ℕ → σ → X → A) : ℕ → ℕ → σ → X → ℝ≥0∞
  | 0, _, _, _ => 0
  | k + 1, n, s, x =>
      ∑' d : ℕ, M.demand s d *
        (stage (post x (π n s x) d) +
          (M.α : ℝ≥0∞) * ∑ s' : σ, M.trans s s' *
            Model.costToGo M post stage π k (n + 1) s' (post x (π n s x) d))

end ServiceParts.UnitDecomp
