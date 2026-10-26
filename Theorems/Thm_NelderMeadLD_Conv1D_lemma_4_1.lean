import Mathlib
import Definitions.Def_NelderMeadLD_Conv1D_Algorithm

open Filter Topology

namespace NelderMeadLD.Conv1D

theorem lemma_4_1 (f : ℝ → ℝ) (hf : StrictConvexOn ℝ Set.univ f)
    (xmin : ℝ) (hmin : ∀ y, f xmin ≤ f y) :
    (∀ y1 y2 y3 : ℝ, y1 ≠ y2 → y2 ≠ y3 → y1 ≠ y3 →
        min y1 y3 < y2 → y2 < max y1 y3 → f y2 ≤ f y1 → f y2 ≤ f y3 →
        min y1 y3 < xmin ∧ xmin < max y1 y3) ∧
    (∀ y1 y2 : ℝ, y1 ≠ y2 → xmin ∈ Set.uIcc y1 y2 →
        ∀ ξ1 ξ2 : ℝ, 1 ≤ ξ1 → ξ1 < ξ2 →
          f (y2 + ξ1 * (y1 - y2)) < f (y2 + ξ2 * (y1 - y2))) ∧
    Continuous f := by sorry

end NelderMeadLD.Conv1D

