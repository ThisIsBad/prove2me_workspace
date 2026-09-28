import Mathlib

namespace LogRegretOCO.FTAL
theorem surrogate_regret_le {n : ℕ} (P : Set (EuclideanSpace ℝ (Fin n)))
    (f fT : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n)) (T : ℕ)
    (hx : ∀ t ∈ Finset.Icc 1 T, x t ∈ P)
    (heq : ∀ t ∈ Finset.Icc 1 T, f t (x t) = fT t (x t))
    (hle : ∀ t ∈ Finset.Icc 1 T, ∀ y ∈ P, fT t y ≤ f t y) :
    ∀ u ∈ P,
      ∑ t ∈ Finset.Icc 1 T, f t (x t) - ∑ t ∈ Finset.Icc 1 T, f t u
        ≤ ∑ t ∈ Finset.Icc 1 T, fT t (x t) - ∑ t ∈ Finset.Icc 1 T, fT t u := by sorry
end LogRegretOCO.FTAL

