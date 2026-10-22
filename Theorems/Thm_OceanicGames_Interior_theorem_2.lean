import Mathlib
import Definitions.Def_OceanicGames_Interior_Basic
open MeasureTheory Filter Topology

namespace OceanicGames.Interior

/-- Theorem 2, (4.7), p. 11: `Φ(y) = α (d/dy) E{F(y)}` for `0 ≤ y ≤ w(M) + α` (one-sided at the
endpoints). -/
theorem theorem_2 {m : ℕ} (α : ℝ) (w : Fin m → ℝ) (hα : 0 < α) (hw : ∀ j, 0 ≤ w j)
    (y : ℝ) (hy : y ∈ Set.Icc 0 (wsum w Finset.univ + α)) :
    HasDerivWithinAt (expPivotLoc α w) (oceanValue y α w / α)
      (Set.Icc 0 (wsum w Finset.univ + α)) y := by sorry

end OceanicGames.Interior

