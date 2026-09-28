import Mathlib
open Filter Topology

namespace NonsmoothNewton.Shared

/-- The B-limit set of Qi–Sun (1993), p. 354: all limits `V = lim_i JF(x_i)` of Fréchet
derivatives along sequences `x_i → x` of points `x_i ∈ D_F` where `F` is differentiable. -/
def bJac {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (F : E → G) (x : E) : Set (E →L[ℝ] G) :=
  {V | ∃ u : ℕ → E, Tendsto u atTop (𝓝 x) ∧ (∀ k, DifferentiableAt ℝ F (u k)) ∧
    Tendsto (fun k => fderiv ℝ F (u k)) atTop (𝓝 V)}

/-- Clarke's generalized Jacobian, Qi–Sun (1993), Eq. (2.1), p. 354:
`∂F(x) = co { lim_{x_i → x, x_i ∈ D_F} JF(x_i) }`, the convex hull of the B-limit set. -/
def clarkeJac {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (F : E → G) (x : E) : Set (E →L[ℝ] G) :=
  convexHull ℝ (bJac F x)

end NonsmoothNewton.Shared
