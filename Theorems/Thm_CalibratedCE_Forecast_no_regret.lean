import Mathlib
import Definitions.Def_CalibratedCE_Forecast_IsDist
import Definitions.Def_CalibratedCE_Forecast_Regret

namespace CalibratedCE.Forecast

theorem no_regret (k : ℕ) (L w : ℕ → Fin k → ℝ)
    (hL : ∀ t i, 0 ≤ L t i ∧ L t i ≤ 1)
    (hw : ∀ t, IsDist (w t))
    (hflow : ∀ t i, w t i * ∑ j, Rg L w t i j = ∑ j, w t j * Rg L w t j i)
    (T : ℕ) (i j : Fin k) :
    Rg L w T i j ≤ Real.sqrt (2 * k * T) := by sorry

end CalibratedCE.Forecast
