import Mathlib
import Definitions.Def_KarpPapadimitriou_Generator_Hyperplanes

namespace KarpPapadimitriou.Generator

/-- Lemma 5: projecting onto one additional independent small hyperplane increases the
distance by at most the displayed factor. -/
theorem lemma_5 (n P j : ℕ) (c : Fin n → ℤ) (k : ℤ)
    (H : Fin (j + 2) → (Fin n → ℤ) × ℤ)
    (r : EuclideanSpace ℝ (Fin n))
    (hsmall : ∀ i, SmallHyperplane P (H i).1 (H i).2)
    (hind : IndependentNormals H)
    (hr : ∀ i : Fin (j + 2), i.val ≤ j → r ∈ hyperplane (H i).1 (H i).2) :
    Metric.infDist r (flat H) ≤
      ((2 : ℝ) ^ tParam n P c k - 1) *
        hyperplaneDistance (H ⟨j + 1, by omega⟩).1 (H ⟨j + 1, by omega⟩).2 r := by sorry

end KarpPapadimitriou.Generator

