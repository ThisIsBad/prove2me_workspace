import Mathlib
import Definitions.Def_WardropTraffic_MeanSpeed_Setting

namespace WardropTraffic.MeanSpeed

theorem time_mean_second_moment {C : ℕ} (q v : Fin C → ℝ)
    (hC : 0 < C) (hq : ∀ i, 0 < q i) (hv : ∀ i, 0 < v i) :
    timeMean q v = (∑ i, spaceFreq q v i * v i ^ 2) / spaceMean q v := by sorry

end WardropTraffic.MeanSpeed

