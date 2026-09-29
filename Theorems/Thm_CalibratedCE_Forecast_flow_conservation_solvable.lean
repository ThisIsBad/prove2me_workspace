import Mathlib
import Definitions.Def_CalibratedCE_Forecast_IsDist

namespace CalibratedCE.Forecast

theorem flow_conservation_solvable (k : ℕ) (hk : 0 < k) (R : Fin k → Fin k → ℝ)
    (hR : ∀ i j, 0 ≤ R i j) :
    ∃ w : Fin k → ℝ, IsDist w ∧ ∀ i, w i * ∑ j, R i j = ∑ j, w j * R j i := by sorry

end CalibratedCE.Forecast
