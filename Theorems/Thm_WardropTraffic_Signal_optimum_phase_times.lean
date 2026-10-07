import Mathlib
import Definitions.Def_WardropTraffic_Signal_Setting

namespace WardropTraffic.Signal

theorem optimum_phase_times (lam mu xi eta : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (hlm : mu ≤ lam) (hxi0 : 0 < xi) (hxi1 : xi < 1) (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsum : 1 < xi + eta) :
    (0 < cornerD lam mu xi eta →
        ∀ z ∈ feasibleXY xi eta, delayT lam mu xi eta ≤ delayT lam mu z.1 z.2) ∧
      (cornerD lam mu xi eta ≤ 0 →
        (edgeRoot lam mu eta, eta) ∈ feasibleXY xi eta ∧
          ∀ z ∈ feasibleXY xi eta,
            delayT lam mu (edgeRoot lam mu eta) eta ≤ delayT lam mu z.1 z.2) := by sorry

end WardropTraffic.Signal

