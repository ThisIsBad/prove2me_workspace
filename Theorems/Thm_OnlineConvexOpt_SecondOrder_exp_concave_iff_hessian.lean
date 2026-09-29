import Mathlib
import Definitions.Def_OnlineConvexOpt_SecondOrder_ExpConcave

open OnlineConvexOpt.SecondOrder

namespace OnlineConvexOpt.SecondOrder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Lemma 4.2 (Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 59, PDF p. 81). A twice-differentiable function `f : E → ℝ` is
`α`-exp-concave at `x` (`IsExpConcaveAt`, the pointwise Hessian formulation of `g(y) =
exp(-α f(y))` being concave to second order at `x`) if and only if `∇²f(x) ⪰ α∇f(x)∇f(x)^⊤`.
The matrix inequality is stated as a comparison of the two quadratic forms it induces: for every
direction `v`, `v^⊤∇²f(x)v ≥ α(∇f(x)^⊤v)^2`, where `v^⊤∇²f(x)v` is the iterated Fréchet
derivative `(fderiv ℝ (fderiv ℝ f) x) v v` and `∇f(x)^⊤v` is the differential `(fderiv ℝ f x) v`.
-/
theorem exp_concave_iff_hessian (α : ℝ) (f : E → ℝ) (x : E) (hf : ContDiffAt ℝ 2 f x) :
    IsExpConcaveAt α f x ↔
      ∀ v : E, α * ((fderiv ℝ f x) v) ^ 2 ≤ (fderiv ℝ (fderiv ℝ f) x) v v := by sorry

end OnlineConvexOpt.SecondOrder

