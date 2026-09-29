import Mathlib

namespace ProxNewton.Inexact

open scoped RealInnerProductSpace

variable {n : ℕ}

open Classical in
/-- The nonsmooth part, given by its effective domain `D` and its values `h` on `D`, is a proper
closed convex function: `D` is nonempty and convex, `h` is convex on `D`, and the extended-valued
function equal to `h` on `D` and to `+∞` off `D` is lower semicontinuous. -/
def IsProperClosedConvex (D : Set (EuclideanSpace ℝ (Fin n)))
    (h : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  D.Nonempty ∧ Convex ℝ D ∧ ConvexOn ℝ D h ∧
    LowerSemicontinuous (fun x => if x ∈ D then (h x : EReal) else ⊤)

/-- `y` is a minimizer of `h(y) + ½‖y - v‖²` over the effective domain `D` of `h`
(Lee–Sun–Saunders, Eq. (2.1)). -/
def IsProxPoint (D : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → ℝ)
    (v y : EuclideanSpace ℝ (Fin n)) : Prop :=
  y ∈ D ∧ ∀ z ∈ D, h y + ‖y - v‖ ^ 2 / 2 ≤ h z + ‖z - v‖ ^ 2 / 2

/-- The proximal mapping `prox_h(v) = argmin_y h(y) + ½‖y - v‖²` (Eq. (2.1)), with `h = +∞`
off `D`. For a proper closed convex `h` the minimizer exists and is unique for every `v`, so the
choice is the paper's `prox_h(v)`; otherwise it is an unspecified point. -/
noncomputable def prox (D : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → ℝ)
    (v : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  Classical.epsilon (IsProxPoint D h v)

/-- The composite gradient step (Eq. (2.3)) with step length `t` on the composite function
`g + h` (smooth part `g`, nonsmooth part `h` with domain `D`):
`G_t(x) = (1/t)(x - prox_{t h}(x - t ∇g(x)))`. The paper's `Gf` is the case `t = 1`. -/
noncomputable def compGradStep (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → ℝ) (t : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  t⁻¹ • (x - prox D (fun y => t * h y) (x - t • gradient g x))

/-- `G_{f/M}`: the composite gradient step with unit step length on the composite function
`f/M = g/M + h/M`, i.e. `x - prox_{h/M}(x - ∇g(x)/M)`. -/
noncomputable def scaledStep (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → ℝ) (M : ℝ) :
    EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
  compGradStep (fun y => g y / M) D (fun y => h y / M) 1

/-- The Hessian `∇²g(x)`, the derivative of the gradient map, as a linear operator. -/
noncomputable def hessian (g : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  fderiv ℝ (gradient g) x

/-- The second-order model of `g` at `x_k` with the exact Hessian `H_k = ∇²g(x_k)` (p. 5):
`ĝ_k(y) = g(x_k) + ∇g(x_k)ᵀ(y - x_k) + ½ (y - x_k)ᵀ ∇²g(x_k) (y - x_k)`. -/
noncomputable def quadModel (g : EuclideanSpace ℝ (Fin n) → ℝ) (xk : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  fun y => g xk + ⟪gradient g xk, y - xk⟫ + (1 / 2) * ⟪y - xk, hessian g xk (y - xk)⟫

end ProxNewton.Inexact
