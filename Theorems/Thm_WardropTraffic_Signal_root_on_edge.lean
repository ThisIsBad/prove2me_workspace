import Mathlib
import Definitions.Def_WardropTraffic_Signal_Setting

namespace WardropTraffic.Signal

theorem root_on_edge (lam mu xi eta : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (hxi0 : 0 < xi) (heta0 : 0 < eta) (hD : cornerD lam mu xi eta < 0) :
    lam * edgeRoot lam mu eta ^ 2 - mu * eta ^ 2 - 2 * lam * edgeRoot lam mu eta * (1 - eta) = 0 ∧
      0 < edgeRoot lam mu eta ∧ edgeRoot lam mu eta < xi ∧
      ∀ x : ℝ, 0 < x → x < xi → lam * x ^ 2 - mu * eta ^ 2 - 2 * lam * x * (1 - eta) = 0 →
        x = edgeRoot lam mu eta := by sorry

end WardropTraffic.Signal

