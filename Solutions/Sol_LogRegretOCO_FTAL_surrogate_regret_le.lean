import Mathlib

namespace LogRegretOCO.FTAL

end LogRegretOCO.FTAL

open LogRegretOCO.FTAL

theorem solution {n : ℕ} (P : Set (EuclideanSpace ℝ (Fin n)))
    (f fT : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n)) (T : ℕ)
    (hx : ∀ t ∈ Finset.Icc 1 T, x t ∈ P)
    (heq : ∀ t ∈ Finset.Icc 1 T, f t (x t) = fT t (x t))
    (hle : ∀ t ∈ Finset.Icc 1 T, ∀ y ∈ P, fT t y ≤ f t y) :
    ∀ u ∈ P,
      ∑ t ∈ Finset.Icc 1 T, f t (x t) - ∑ t ∈ Finset.Icc 1 T, f t u
        ≤ ∑ t ∈ Finset.Icc 1 T, fT t (x t) - ∑ t ∈ Finset.Icc 1 T, fT t u := by
  intro u hu
  have h1 : ∑ t ∈ Finset.Icc 1 T, f t (x t) = ∑ t ∈ Finset.Icc 1 T, fT t (x t) :=
    Finset.sum_congr rfl heq
  have h2 : ∑ t ∈ Finset.Icc 1 T, fT t u ≤ ∑ t ∈ Finset.Icc 1 T, f t u :=
    Finset.sum_le_sum (fun t ht => hle t ht u hu)
  linarith
