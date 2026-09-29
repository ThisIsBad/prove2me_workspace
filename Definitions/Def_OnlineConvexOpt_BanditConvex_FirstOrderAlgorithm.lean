import Mathlib

namespace OnlineConvexOpt.BanditConvex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Definition 6.4 (Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 107, PDF p. 129). `A`, an algorithm mapping a full sequence of
differentiable cost functions to a play sequence (`x_1 ← A(∅)`, `x_t ← A(f_1, ..., f_{t-1})`,
here `A f t` for round `t`), is a *first order online algorithm* if (1) it is non-anticipating —
round `t`'s decision depends only on `f_1, ..., f_{t-1}`, which Definition 6.4's opening sentence
presupposes of every OCO algorithm before stating the "first order" bullets — and (2) it treats
every cost function only through its gradient at the point it actually plays: for every cost
sequence `f` and every sequence `g` of linear functionals `g τ = fun y => ⟪∇f_τ(x_τ), y⟫` built
from the gradients of `f` at the points `x_τ = A f τ` that `A` itself plays on `f`, `A` produces
the same decision at every round on `g` as it does on `f` (`A(f_1, ..., f_{t-1}) = A(f̂_1, ...,
f̂_{t-1})` in the book's notation, `f̂_τ(x) = ∇f_τ(x_τ)^⊤x`). Clause (1) mirrors
`OnlineConvexOpt.FirstOrder.IsOnlineAlgorithm`'s non-anticipation conjunct for the same function
type, without a decision-set membership clause since Definition 6.4 states none. -/
def IsFirstOrderOnlineAlgorithm (A : (ℕ → E → ℝ) → ℕ → E) : Prop :=
  (∀ (f f' : ℕ → E → ℝ) (t : ℕ), (∀ s < t, f s = f' s) → A f t = A f' t) ∧
  ∀ f g : ℕ → E → ℝ,
    (∀ τ : ℕ, ∃ gradfτ : E, HasGradientAt (f τ) gradfτ (A f τ) ∧ ∀ y : E, g τ y = inner ℝ gradfτ y) →
    ∀ t : ℕ, A f t = A g t

end OnlineConvexOpt.BanditConvex
