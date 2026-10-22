import Mathlib
import Definitions.Def_OceanicGames_Limit_Basic

namespace OceanicGames.Limit

open MeasureTheory Set Finset

/-- Equations (3.5)–(3.6): integrate the volume of a predecessor cell
over the pivotal interval for player i. -/
theorem equation_3_5 {m : ℕ} (c alpha : ℝ) (w : Fin m → ℝ) (i : Fin m)
    (S : Finset (Fin m)) (hS : S ⊆ Finset.univ.erase i)
    (hc : 0 ≤ c) (halpha : 0 < alpha) (hw : ∀ j, 0 ≤ w j) :
    (volume (OceanicGames.Interior.pivotSet c alpha w i ∩ orderSet i S)).toReal =
      ∫ t in Set.Icc
        (clamp01 ((c - OceanicGames.Interior.wsum w (insert i S)) / alpha))
        (clamp01 ((c - OceanicGames.Interior.wsum w S) / alpha)),
        t ^ S.card * (1 - t) ^ (m - S.card - 1) := by sorry

end OceanicGames.Limit

