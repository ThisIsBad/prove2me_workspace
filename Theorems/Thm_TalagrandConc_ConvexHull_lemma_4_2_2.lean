import Mathlib
import Definitions.Def_TalagrandConc_ConvexHull_Basic

namespace TalagrandConc.ConvexHull

/-- Talagrand (1995), p. 127, Lemma 4.2.2: for `α > 0`, the function `ξ(α, ·)` is
(strictly) increasing and convex on `[0, 1]`, and `ξ(α, u) ≥ α u² / (2(α + 1))` for
`u ∈ [0, 1]`. -/
theorem lemma_4_2_2 (α : ℝ) (hα : 0 < α) :
    StrictMonoOn (xi α) (Set.Icc 0 1) ∧ ConvexOn ℝ (Set.Icc 0 1) (xi α) ∧
      ∀ u ∈ Set.Icc (0 : ℝ) 1, α / (2 * (α + 1)) * u ^ 2 ≤ xi α u := by sorry

end TalagrandConc.ConvexHull

