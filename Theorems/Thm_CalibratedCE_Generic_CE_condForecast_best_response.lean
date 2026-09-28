import Mathlib
import Definitions.Def_CalibratedCE_Generic_Game
import Definitions.Def_CalibratedCE_Generic_Forecasts

namespace CalibratedCE.Generic

theorem CE_condForecast_best_response {m n : ℕ} (u₁ u₂ : Fin m → Fin n → ℝ)
    (D : Fin m → Fin n → ℝ) (hCE : IsCE u₁ u₂ D) :
    (∀ a, 0 < ∑ c, D a c → condForecast₁ D a ∈ Mb u₁ a) ∧
      (∀ b, 0 < ∑ c, D c b → ∀ b',
        ∑ a, condForecast₂ D b a * u₂ a b' ≤ ∑ a, condForecast₂ D b a * u₂ a b) := by sorry

end CalibratedCE.Generic
