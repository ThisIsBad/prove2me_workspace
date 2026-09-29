import Mathlib
import Definitions.Def_CalibratedCE_Generic_Game
import Definitions.Def_CalibratedCE_Shared_Calibration
import Definitions.Def_CalibratedCE_Generic_Forecasts

open Filter Topology

namespace CalibratedCE.Generic

theorem condForecast_calibrated {m n : ℕ} (D : Fin m → Fin n → ℝ) (hD : IsJointDist D)
    (x : ℕ → Fin m) (y : ℕ → Fin n) (hsupp : ∀ t, 0 < D (x t) (y t))
    (hlim : ∀ a b, Tendsto (fun t => empDist x y t a b) atTop (𝓝 (D a b))) :
    (∀ t, IsDist (condForecast₁ D (x t))) ∧ (∀ t, IsDist (condForecast₂ D (y t))) ∧
      Shared.Calibrated (fun t => condForecast₁ D (x t)) y ∧
      Shared.Calibrated (fun t => condForecast₂ D (y t)) x := by sorry

end CalibratedCE.Generic
