import Mathlib
import Definitions.Def_LogRegretOCO_FTAL_IsFTALRun

namespace LogRegretOCO.FTAL
theorem ftal_regret_bound {n : ℕ} (P : Set (EuclideanSpace ℝ (Fin n))) (D G α : ℝ)
    (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n))
    (hPne : P.Nonempty) (hPconv : Convex ℝ P) (hPclosed : IsClosed P)
    (hPbdd : Bornology.IsBounded P)
    (hD : 0 < D) (hdiam : ∀ y ∈ P, ∀ z ∈ P, ‖y - z‖ ≤ D)
    (hG : 0 < G) (hα : 0 < α)
    (hdiff : ∀ t, 1 ≤ t → ∀ y ∈ P, DifferentiableAt ℝ (f t) y)
    (hgrad : ∀ t, 1 ≤ t → ∀ y ∈ P, ‖gradient (f t) y‖ ≤ G)
    (hexp : ∀ t, 1 ≤ t → ConcaveOn ℝ P (fun y => Real.exp (-α * f t y)))
    (hx : IsFTALRun P (1 / 2 * min (1 / (4 * G * D)) α) f x) :
    ∀ T : ℕ, 1 ≤ T → ∀ u ∈ P,
      ∑ t ∈ Finset.Icc 1 T, (f t (x t) - f t u)
        ≤ 64 * (1 / α + G * D) * n * (Real.log T + 1) := by sorry
end LogRegretOCO.FTAL

