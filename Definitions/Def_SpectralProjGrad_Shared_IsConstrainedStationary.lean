import Mathlib

namespace SpectralProjGrad.Shared

/-- `x̄` is a constrained stationary point of `f` on `Ω`: `⟨∇f(x̄), x - x̄⟩ ≥ 0` for all `x ∈ Ω`. -/
def IsConstrainedStationary {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (xbar : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ x ∈ Ω, inner ℝ (gradient f xbar) (x - xbar) ≥ 0

end SpectralProjGrad.Shared
