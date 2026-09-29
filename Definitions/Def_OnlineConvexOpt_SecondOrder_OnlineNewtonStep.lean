import Mathlib

namespace OnlineConvexOpt.SecondOrder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The squared (semi)norm induced by an operator `A : E →L[ℝ] E`, `‖v‖²_A = ⟪v, A v⟫`. For the
positive semidefinite `A_t` of Algorithm 12 this is the norm `‖·‖_{A_t}` used by the algorithm's
generalized projection. -/
noncomputable def quadForm (A : E →L[ℝ] E) (v : E) : ℝ := inner ℝ v (A v)

/-- `IsGeneralizedProjection A K y p`: `p` is a minimizer over `K` of the squared distance to `y`
induced by `A`, i.e. `p ∈ arg min_{x ∈ K} ‖y - x‖²_A` — the projection `Π^A_K` of Algorithm 12
(book p. 62, PDF p. 84), in place of the Euclidean metric projection `Π_K` of online gradient
descent (`OnlineConvexOpt.FirstOrder.IsMetricProjection`). -/
def IsGeneralizedProjection (A : E →L[ℝ] E) (K : Set E) (y p : E) : Prop :=
  p ∈ K ∧ ∀ z ∈ K, quadForm A (y - p) ≤ quadForm A (y - z)

/-- `(x, g, A)` is a run of online Newton step (Algorithm 12, book p. 62, PDF p. 84) on cost
functions `f` over the decision set `K`, with parameters `γ, ε > 0`: the initial decision `x 0`
lies in `K`; `A 0 = ε • id` (`A_0 = εI_n`); at every round `t`, `g t` is the gradient of `f t` at
the played point `x t` (`∇t := ∇f_t(x_t)`); the running matrix updates by the rank-one term
`A (t + 1) = A t + ∇_t∇_t^⊤` (`InnerProductSpace.rankOne ℝ (g t) (g t)` is the operator
`v ↦ ⟪g t, v⟫ • g t`, matching the outer product); and the next decision `x (t + 1)` is the
`A (t + 1)`-generalized projection onto `K` of the Newton step
`y_{t+1} = x_t - γ⁻¹ A_{t+1}^{-1} ∇_t` (`(A (t + 1)).inverse` is Mathlib's total inverse of a
continuous linear map, agreeing with the matrix inverse when `A (t + 1)` is invertible, which
holds throughout the run since every `A (t + 1)` is positive definite: `A 0 ≻ 0` and each update
adds a positive semidefinite rank-one term). Indices are shifted down by one from the book's
`t ∈ {1, ..., T}` to match the 0-indexed convention of `OnlineConvexOpt.FirstOrder.RegretT`: our
`A (t + 1)` is the book's `A_{t+1}` built from rounds `1, ..., t+1`, i.e. our rounds `0, ..., t`. -/
def IsOnlineNewtonStep (K : Set E) (γ ε : ℝ) (f : ℕ → E → ℝ)
    (x g : ℕ → E) (A : ℕ → E →L[ℝ] E) : Prop :=
  x 0 ∈ K ∧ A 0 = ε • (ContinuousLinearMap.id ℝ E) ∧
    (∀ t : ℕ, HasGradientAt (f t) (g t) (x t)) ∧
    (∀ t : ℕ, A (t + 1) = A t + InnerProductSpace.rankOne ℝ (g t) (g t)) ∧
    (∀ t : ℕ, IsGeneralizedProjection (A (t + 1)) K
      (x t - γ⁻¹ • (A (t + 1)).inverse (g t)) (x (t + 1)))

end OnlineConvexOpt.SecondOrder
