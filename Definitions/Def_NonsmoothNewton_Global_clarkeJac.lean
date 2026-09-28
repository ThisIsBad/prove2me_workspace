import Mathlib

namespace NonsmoothNewton.Global

open Filter Topology

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]

/-- The differentiability set `D_F = {y | F is differentiable at y}` (Qi–Sun 1993, p. 354). -/
def diffSet (F : E → G) : Set E := {y | DifferentiableAt ℝ F y}

/-- The B-limit set: all limits `lim JF(x_i)` of derivatives along sequences `x_i → x` with
`x_i ∈ D_F` (Qi–Sun 1993, p. 354, inside Eq. (2.1)). -/
def bJac (F : E → G) (x : E) : Set (E →L[ℝ] G) :=
  {V | ∃ u : ℕ → E, Tendsto u atTop (𝓝 x) ∧ (∀ k, DifferentiableAt ℝ F (u k)) ∧
    Tendsto (fun k => fderiv ℝ F (u k)) atTop (𝓝 V)}

/-- Clarke's generalized Jacobian `∂F(x) = co{lim_{x_i → x, x_i ∈ D_F} JF(x_i)}`
(Qi–Sun 1993, p. 354, Eq. (2.1)): the convex hull of the B-limit set. -/
def clarkeJac (F : E → G) (x : E) : Set (E →L[ℝ] G) :=
  convexHull ℝ (bJac F x)

end NonsmoothNewton.Global
