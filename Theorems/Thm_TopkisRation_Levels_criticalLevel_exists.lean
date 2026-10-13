import Mathlib
import Definitions.Def_TopkisRation_Levels_Model

namespace TopkisRation.Levels

theorem criticalLevel_exists {n : ℕ} (M : Model n) (hM : M.Standing) (t : ℕ)
    (ht : t ∈ Finset.Icc 1 M.k) :
    ∀ j : Fin n, ∃! zbar : WithTop ℝ, IsCriticalLevel (M.levelObj t j) zbar := by sorry

end TopkisRation.Levels

