import Mathlib
import Definitions.Def_WardropTraffic_Signal_Setting

namespace WardropTraffic.Signal

theorem corner_min_of_neg_partials (lam mu xi eta : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (hsum : 1 < xi + eta)
    (hx : lam * xi ^ 2 - mu * eta ^ 2 - 2 * lam * xi * (1 - eta) < 0)
    (hy : mu * eta ^ 2 - lam * xi ^ 2 - 2 * mu * eta * (1 - xi) < 0) :
    ∀ z ∈ feasibleXY xi eta, delayT lam mu xi eta ≤ delayT lam mu z.1 z.2 := by sorry

end WardropTraffic.Signal

