import Mathlib
import Definitions.Def_CalibratedCE_Generic_Game
import Definitions.Def_CalibratedCE_Generic_Forecasts

open Filter Topology

namespace CalibratedCE.Generic

theorem pert_strict_best_reply {m n : ℕ} (u₁ : Fin m → Fin n → ℝ) (a : Fin m)
    (pstar q : Fin n → ℝ) (hpstar : pstar ∈ Mb u₁ a) (hq : IsDist q)
    (hqa : ∀ a', a' ≠ a → ∑ b, q b * u₁ a' b < ∑ b, q b * u₁ a b) :
    (∀ i : ℕ, 1 ≤ i → IsDist (pert pstar q i) ∧
        ∀ a', a' ≠ a → ∑ b, pert pstar q i b * u₁ a' b < ∑ b, pert pstar q i b * u₁ a b) ∧
      Tendsto (pert pstar q) atTop (𝓝 pstar) := by sorry

end CalibratedCE.Generic
