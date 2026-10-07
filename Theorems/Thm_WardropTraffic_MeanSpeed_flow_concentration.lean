import Mathlib
import Definitions.Def_WardropTraffic_MeanSpeed_Setting

namespace WardropTraffic.MeanSpeed

theorem flow_concentration {C : ℕ} (q v : Fin C → ℝ)
    (hC : 0 < C) (hq : ∀ i, 0 < q i) (hv : ∀ i, 0 < v i) :
    (∀ i, conc q v i * v i = q i) ∧
      totalFlow q = totalConc q v * spaceMean q v := by sorry

end WardropTraffic.MeanSpeed

