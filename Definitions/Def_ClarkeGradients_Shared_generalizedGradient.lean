import Mathlib

open Filter Topology

namespace ClarkeGradients.Shared

/-- The set of limits `lim ∇f(x + hᵢ)` of Clarke (1975), Definition (1.1): all `ζ` such that
for some sequence `hᵢ → 0`, `f` is differentiable at every `x + hᵢ` and `∇f(x + hᵢ) → ζ`. -/
def gradientLimits {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {ζ | ∃ h : ℕ → EuclideanSpace ℝ (Fin n), Tendsto h atTop (𝓝 0) ∧
    (∀ i, DifferentiableAt ℝ f (x + h i)) ∧
    Tendsto (fun i => gradient f (x + h i)) atTop (𝓝 ζ)}

/-- Clarke (1975), Definition (1.1): the *generalized gradient* `∂f(x)` is the convex hull of
the set of limits of the form `lim ∇f(x + hᵢ)`, where `hᵢ → 0`. -/
def generalizedGradient {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  convexHull ℝ (gradientLimits f x)

end ClarkeGradients.Shared
