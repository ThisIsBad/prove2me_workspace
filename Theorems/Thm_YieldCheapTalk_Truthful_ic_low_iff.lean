import Mathlib
import Definitions.Def_YieldCheapTalk_Truthful_Setting
open MeasureTheory

namespace YieldCheapTalk.Truthful
theorem ic_low_iff (M : Model) (hM : M.Standing) :
    (M.Qr (M.theta .L) (M.a .H) - M.Qr (M.theta .H) (M.a .H)) * M.mu .H .L ≥
          (M.Qr (M.theta .H) (M.a .L) - M.Qr (M.theta .L) (M.a .L)) * M.mu .L .L ↔
      (1 + M.eta * (1 / M.theta .H + 1 / M.theta .L - 1)) * M.w ≤
        ∑ m, M.mu m .L * M.a m := by sorry
end YieldCheapTalk.Truthful

