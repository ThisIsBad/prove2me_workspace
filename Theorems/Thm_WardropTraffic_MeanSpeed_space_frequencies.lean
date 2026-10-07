import Mathlib
import Definitions.Def_WardropTraffic_MeanSpeed_Setting

namespace WardropTraffic.MeanSpeed

theorem space_frequencies {C : ℕ} (q v : Fin C → ℝ)
    (hC : 0 < C) (hq : ∀ i, 0 < q i) (hv : ∀ i, 0 < v i) :
    (∑ i, spaceFreq q v i * (v i - spaceMean q v)) = 0 := by sorry

end WardropTraffic.MeanSpeed

