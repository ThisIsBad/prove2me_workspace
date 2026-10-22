import Mathlib
import Definitions.Def_OceanicGames_Interior_Basic
open MeasureTheory Filter Topology

namespace OceanicGames.Interior

/-- §2, p. 5, last paragraph: the pivot sets `A_1, …, A_m` are disjoint up to a set of measure
zero. -/
theorem pivotSet_ae_disjoint {m : ℕ} (c α : ℝ) (w : Fin m → ℝ) (hα : 0 < α)
    (hw : ∀ j, 0 ≤ w j) (hc0 : 0 ≤ c) (hcW : c ≤ wsum w Finset.univ + α)
    (i j : Fin m) (hij : i ≠ j) :
    volume (pivotSet c α w i ∩ pivotSet c α w j) = 0 := by sorry

end OceanicGames.Interior

