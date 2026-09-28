import Mathlib

namespace OnlineConvexOpt.FirstOrder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Regret of a decision sequence `x` against cost functions `f` over the first `T` rounds
(indexed `0, ..., T - 1`, i.e. the book's rounds `1, ..., T` shifted down by one), as in Eq.
(1.1)/(1.2): the cumulative cost incurred minus the cost of the best fixed decision in `K` in
hindsight. -/
noncomputable def RegretT (K : Set E) (f : ℕ → E → ℝ) (x : ℕ → E) (T : ℕ) : ℝ :=
  (∑ t ∈ Finset.range T, f t (x t)) - ⨅ y ∈ K, ∑ t ∈ Finset.range T, f t y

/-- `p` is a metric projection of `y` onto `K`: a point of `K` at least as close to `y` as
every other point of `K`. This is the projection step `Π_K` used by Algorithm 8. -/
def IsMetricProjection (K : Set E) (y p : E) : Prop :=
  p ∈ K ∧ ∀ z ∈ K, dist y p ≤ dist y z

/-- `(x, g)` is a run of online gradient descent (Algorithm 8) on cost functions `f` over the
decision set `K`, with step sizes `η`: the initial decision `x 0` lies in `K`; at every round
`t`, `g t` is the gradient of `f t` at the played point `x t` (`∇t := ∇f_t(x_t)` in the book's
notation), and the next decision `x (t + 1)` is a metric projection onto `K` of the gradient
step `x t - η t • g t` (`y_{t+1} = x_t - η_t ∇_t`, `x_{t+1} = Π_K(y_{t+1})`). -/
def IsOnlineGradientDescent (K : Set E) (f : ℕ → E → ℝ) (η : ℕ → ℝ) (x g : ℕ → E) : Prop :=
  x 0 ∈ K ∧ ∀ t : ℕ, HasGradientAt (f t) (g t) (x t) ∧
    IsMetricProjection K (x t - η t • g t) (x (t + 1))

end OnlineConvexOpt.FirstOrder
