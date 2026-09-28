import Mathlib
import Definitions.Def_OnlineConvexOpt_ProjectionFree_LinearOracle

open scoped InnerProductSpace

namespace OnlineConvexOpt.ProjectionFree

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Algorithm 27 line 4 (Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 133, PDF p. 155): the aggregate regularized function
`F_t(x) = η ∑_{τ=1}^{t-1} ⟪∇_τ, x⟫ + ‖x - x_1‖²`, where `gradf τ = ∇f_τ(x_τ)` is the gradient of
the round-`τ` cost function at the point actually played. -/
noncomputable def AggregateFunction (gradf : ℕ → E) (x1 : E) (η : ℝ) (t : ℕ) (x : E) : ℝ :=
  η * (∑ τ ∈ Finset.Ico 1 t, ⟪gradf τ, x⟫_ℝ) + ‖x - x1‖ ^ 2

/-- The gradient of `AggregateFunction gradf x1 η t` at `x`: `η ∑_{τ=1}^{t-1} ∇_τ + 2(x - x_1)`,
the closed form Algorithm 27 line 5 uses directly (`∇F_t(x_t)`), rather than an abstract
`HasGradientAt` witness, since the book computes it explicitly. -/
noncomputable def AggregateGradient (gradf : ℕ → E) (x1 : E) (η : ℝ) (t : ℕ) (x : E) : E :=
  η • (∑ τ ∈ Finset.Ico 1 t, gradf τ) + (2 : ℝ) • (x - x1)

/-- `(x, v)` is a run of the online conditional gradient algorithm (Algorithm 27, p. 133, PDF p.
155) on `K`, cost sequence `f`, with initial point `x_1`, parameter `η`, and step sizes `σ`: the
first play is `x_1` (line 1); at every round `t ≥ 1`, `gradf t` is the gradient of `f_t` at the
played point `x_t` (`∇_t := ∇f_t(x_t)`, used both to observe the round and to build `F_{t+1}`),
`v_t` solves the linear-minimization oracle in the direction `∇F_t(x_t)` (line 5), and the next
point is `x_{t+1} = (1 - σ_t)x_t + σ_t v_t` (line 6). -/
def IsOnlineConditionalGradientRun (K : Set E) (f : ℕ → E → ℝ) (gradf : ℕ → E) (x1 : E) (η : ℝ)
    (σ : ℕ → ℝ) (x v : ℕ → E) : Prop :=
  x 1 = x1 ∧ x1 ∈ K ∧
    (∀ t : ℕ, 1 ≤ t → HasGradientAt (f t) (gradf t) (x t)) ∧
    (∀ t : ℕ, 1 ≤ t → IsLinearMinimizer K (AggregateGradient gradf x1 η t (x t)) (v t)) ∧
    (∀ t : ℕ, 1 ≤ t → x (t + 1) = (1 - σ t) • x t + σ t • v t)

end OnlineConvexOpt.ProjectionFree
