import Mathlib
import Definitions.Def_CalibratedCE_Forecast_CalibScoreH

namespace CalibratedCE.Forecast

theorem l1_calib_le_sqrt_l2 {n : ℕ} (h : List ((Fin n → ℝ) × Fin n)) (j : Fin n) :
    calibScoreHj h j ≤ Real.sqrt (calibScore2Hj h j) := by sorry

end CalibratedCE.Forecast

