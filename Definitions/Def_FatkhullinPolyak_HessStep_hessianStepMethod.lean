import Mathlib

namespace FatkhullinPolyak.HessStep

/-- The Hessian quadratic form `⟨∇²f(x) v, v⟩`, read off the second Fréchet derivative:
`fderiv ℝ (fderiv ℝ f) x` is the Hessian of `f` at `x` as a bilinear map, applied to `(v, v)`.
Where `f` is not twice differentiable at `x` this is Lean's junk value `0`; every statement of
the mission assumes `f` and `fderiv ℝ f` differentiable everywhere. -/
noncomputable def hessQuad {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x v : EuclideanSpace ℝ (Fin n)) : ℝ :=
  fderiv ℝ (fderiv ℝ f) x v v

/-- The step size of the method (6.1) at the point `x`:
`γ(x) = ‖∇f(x)‖² / ⟨∇²f(x)∇f(x), ∇f(x)⟩`. At a stationary point both numerator and
denominator vanish and Lean's division gives `γ(x) = 0`, so the method stays put. -/
noncomputable def hessStep {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ‖gradient f x‖ ^ 2 / hessQuad f x (gradient f x)

/-- The iterates of the gradient method (6.1) with the Hessian step size, started at `x₀`:
`x_{j+1} = x_j − γ(x_j) ∇f(x_j)`. -/
noncomputable def hessIter {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x₀ : EuclideanSpace ℝ (Fin n)) : ℕ → EuclideanSpace ℝ (Fin n)
  | 0 => x₀
  | j + 1 => hessIter f x₀ j - hessStep f (hessIter f x₀ j) • gradient f (hessIter f x₀ j)

/-- The iterates of the damped version of (6.1), with `γ_j` replaced by `σ γ_j`, started at
`x₀`: `x_{j+1} = x_j − σ γ(x_j) ∇f(x_j)`. -/
noncomputable def dampedHessIter {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (σ : ℝ)
    (x₀ : EuclideanSpace ℝ (Fin n)) : ℕ → EuclideanSpace ℝ (Fin n)
  | 0 => x₀
  | j + 1 => dampedHessIter f σ x₀ j -
      (σ * hessStep f (dampedHessIter f σ x₀ j)) • gradient f (dampedHessIter f σ x₀ j)

end FatkhullinPolyak.HessStep
