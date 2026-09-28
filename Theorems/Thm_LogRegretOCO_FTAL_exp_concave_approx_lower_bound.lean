import Mathlib

namespace LogRegretOCO.FTAL
theorem exp_concave_approx_lower_bound {n : ℕ} (P : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (D G α β : ℝ)
    (hPconv : Convex ℝ P) (hD : 0 < D) (hG : 0 < G) (hα : 0 < α)
    (hdiam : ∀ x ∈ P, ∀ y ∈ P, ‖x - y‖ ≤ D)
    (hdiff : ∀ x ∈ P, DifferentiableAt ℝ f x)
    (hgrad : ∀ x ∈ P, ‖gradient f x‖ ≤ G)
    (hexp : ConcaveOn ℝ P (fun x => Real.exp (-α * f x)))
    (hβ0 : 0 < β) (hβ : β ≤ 1 / 2 * min (1 / (4 * G * D)) α) :
    ∀ x ∈ P, ∀ y ∈ P,
      f y + inner ℝ (gradient f y) (x - y) + β / 2 * (inner ℝ (gradient f y) (x - y)) ^ 2
        ≤ f x := by sorry
end LogRegretOCO.FTAL

