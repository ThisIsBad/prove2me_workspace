import Mathlib
import Definitions.Def_TopkisRation_Levels_Model
import Definitions.Def_TopkisRation_Levels_Split

namespace TopkisRation.Levels

theorem eq_6 {n : ℕ} (M : Model n) (hM : M.Standing) (t : ℕ) (ht : t ∈ Finset.Icc 1 M.k)
    (z : ℝ) (hz : 0 ≤ z) (B : Fin n → ℝ) (hB : 0 ≤ B) :
    M.f t z B = sInf ((fun w => M.fw t w z B) '' Set.Icc (max (z - ∑ j, B j) 0) z) ∧
    ∃ w ∈ Set.Icc (max (z - ∑ j, B j) 0) z, M.fw t w z B = M.f t z B := by sorry

end TopkisRation.Levels

