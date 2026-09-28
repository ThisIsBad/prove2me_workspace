import Mathlib

namespace SpectralProjGrad.Shared

/-- The scaled projected gradient `g_t(x) = P(x - t g(x)) - x`, where `g = ∇f` is the gradient
of `f` and `P` is a map on `ℝⁿ` (in every statement of the mission, the projection onto `Ω`). -/
noncomputable def scaledProjGrad {n : ℕ}
    (P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (t : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  P (x - t • gradient f x) - x

end SpectralProjGrad.Shared
