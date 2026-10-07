import Mathlib
import Definitions.Def_ChvatalArtGallery_FanPartition_Triangulation

namespace ChvatalArtGallery.FanPartition

/-- Proof of the Theorem, p. 40: for n ≥ 6, the least k ≥ 4 such that some inner edge has the
form (j, j + k) exists and satisfies k ≤ 6. -/
theorem least_span_le_six (n : ℕ) (hn : 6 ≤ n) (D : Finset (Sym2 (Fin n)))
    (hD : IsTriangulation n D) :
    ∃ (j : Fin n) (k : ℕ), 4 ≤ k ∧ k ≤ 6 ∧ s(j, shift j k) ∈ D ∧
      ∀ (j' : Fin n) (k' : ℕ), 4 ≤ k' → k' < k → s(j', shift j' k') ∉ D := by sorry

end ChvatalArtGallery.FanPartition

