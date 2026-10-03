import Mathlib

namespace ShorNonsmooth.AlmostDiff

/-- Shor (1985), p. 18, Definition: the set `G(x₀)` of **almost-gradients** of `f` at `x₀`.
A vector `g` is an almost-gradient of `f` at `x₀` if it is an accumulation point (cluster point)
of a sequence of gradients `∇f(x₁), ∇f(x₂), …` where `x_k → x₀` and `f` is differentiable at
every `x_k` (the points `x_k = x₀` are not excluded). -/
def almostGradients {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x₀ : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {g | ∃ xs : ℕ → EuclideanSpace ℝ (Fin n),
      Filter.Tendsto xs Filter.atTop (nhds x₀) ∧
      (∀ k, DifferentiableAt ℝ f (xs k)) ∧
      MapClusterPt g Filter.atTop (fun k => gradient f (xs k))}

end ShorNonsmooth.AlmostDiff
