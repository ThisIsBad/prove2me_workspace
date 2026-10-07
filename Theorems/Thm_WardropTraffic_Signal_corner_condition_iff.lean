import Mathlib
import Definitions.Def_WardropTraffic_Signal_Setting

namespace WardropTraffic.Signal

theorem corner_condition_iff (lam mu xi eta : ℝ) (hlam : 0 < lam) :
    lam * xi ^ 2 - mu * eta ^ 2 - 2 * lam * xi * (1 - eta) < 0 ↔ 0 < cornerD lam mu xi eta := by sorry

end WardropTraffic.Signal

