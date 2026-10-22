import Mathlib
import Definitions.Def_OceanicGames_Limit_Basic

namespace OceanicGames.Limit

open MeasureTheory Set Finset

/-- Equation (3.4): split the pivotal region by the predecessor set. -/
theorem equation_3_4 {m : ℕ} (c alpha : ℝ) (w : Fin m → ℝ) (i : Fin m)
    (hc : 0 ≤ c) (halpha : 0 < alpha) (hw : ∀ j, 0 ≤ w j) :
    OceanicGames.Interior.value c alpha w i =
      ∑ S ∈ (Finset.univ.erase i).powerset,
        (volume (OceanicGames.Interior.pivotSet c alpha w i ∩ orderSet i S)).toReal := by sorry

end OceanicGames.Limit

