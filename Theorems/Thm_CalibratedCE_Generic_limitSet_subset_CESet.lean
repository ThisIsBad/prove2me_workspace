import Mathlib
import Definitions.Def_CalibratedCE_Generic_Game
import Definitions.Def_CalibratedCE_Shared_Calibration
import Definitions.Def_CalibratedCE_Generic_LimitSet

namespace CalibratedCE.Generic

theorem limitSet_subset_CESet {m n : ℕ} (u₁ u₂ : Fin m → Fin n → ℝ) :
    LimitSet u₁ u₂ ⊆ CESet u₁ u₂ := by sorry

end CalibratedCE.Generic
