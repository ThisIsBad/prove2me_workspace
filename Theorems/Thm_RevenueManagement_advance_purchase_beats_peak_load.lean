import Mathlib
import Definitions.Def_RevenueManagement_competition

namespace RevenueManagement

theorem advance_purchase_beats_peak_load (v C α wC : ℝ) (F f : ℝ → ℝ) (hα : 0 < α ∧ α < 1)
    (w2 wh : ℝ) (h2 : w2 ∈ Set.Icc 0 wC) (hw : wh ∈ Set.Icc 0 wC)
    (hf : ∀ w ∈ Set.Icc 0 wC, 0 < f w)
    (hψ : StrictAntiOn (fun w => (v - w) - F w / f w) (Set.Icc 0 wC))
    (h13 : (v - w2) * f w2 - F w2 = 1 / α - 1) (h15 : (v - wh) * f wh - F wh = 0)
    (hopt : ∀ w ∈ Set.Icc 0 wC, advancePurchaseRevenue v C α F w ≤ advancePurchaseRevenue v C α F wh) :
    w2 < wh ∧ peakLoadRevenue v C α F w2 ≤ advancePurchaseRevenue v C α F wh := by sorry

end RevenueManagement
