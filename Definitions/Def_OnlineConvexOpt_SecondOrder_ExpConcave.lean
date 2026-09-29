import Mathlib

namespace OnlineConvexOpt.SecondOrder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Definition 4.1 (Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 58, PDF p. 80). A convex function `f : E → ℝ` is `α`-exp-concave over
`K ⊆ E` if the function `g(x) = exp(-α f(x))` is concave on `K`. -/
def IsExpConcaveOn (α : ℝ) (K : Set E) (f : E → ℝ) : Prop :=
  ConvexOn ℝ K f ∧ ConcaveOn ℝ K (fun x => Real.exp (-α * f x))

/-- The pointwise, second-order notion of exp-concavity "at `x`" that Lemma 4.2 characterizes:
the Hessian of `g(y) = exp(-α f(y))` at `x` is negative semidefinite, i.e. `g` is concave to
second order at `x`. Represented via the iterated Fréchet derivative
`fderiv ℝ (fderiv ℝ g) x : E →L[ℝ] E →L[ℝ] ℝ`, applied to the same direction `v` on both sides
(the quadratic form of a symmetric bilinear form is negative semidefinite iff its diagonal values
are `≤ 0`). -/
def IsExpConcaveAt (α : ℝ) (f : E → ℝ) (x : E) : Prop :=
  ∀ v : E, (fderiv ℝ (fderiv ℝ (fun y => Real.exp (-α * f y))) x) v v ≤ 0

end OnlineConvexOpt.SecondOrder
