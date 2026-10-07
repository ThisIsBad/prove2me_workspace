import Mathlib
import Definitions.Def_WardropTraffic_MeanSpeed_Setting

namespace WardropTraffic.MeanSpeed

theorem time_space_mean_relation {C : ℕ} (q v : Fin C → ℝ)
    (hC : 0 < C) (hq : ∀ i, 0 < q i) (hv : ∀ i, 0 < v i) :
    timeMean q v = spaceMean q v + spaceVar q v / spaceMean q v ∧
      spaceMean q v ≤ timeMean q v ∧
      (timeMean q v = spaceMean q v ↔ ∀ i j, v i = v j) := by sorry

end WardropTraffic.MeanSpeed

