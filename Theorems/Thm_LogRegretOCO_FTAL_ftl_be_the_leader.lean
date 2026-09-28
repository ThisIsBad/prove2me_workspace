import Mathlib
import Definitions.Def_LogRegretOCO_FTAL_IsFTLRun

namespace LogRegretOCO.FTAL
theorem ftl_be_the_leader {n : ℕ} (P : Set (EuclideanSpace ℝ (Fin n)))
    (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n))
    (hx : IsFTLRun P f x) (T : ℕ) :
    ∀ u ∈ P,
      ∑ t ∈ Finset.Icc 1 T, f t (x t) - ∑ t ∈ Finset.Icc 1 T, f t u
        ≤ ∑ t ∈ Finset.Icc 1 T, f t (x t) - ∑ t ∈ Finset.Icc 1 T, f t (x (t + 1)) := by sorry
end LogRegretOCO.FTAL

