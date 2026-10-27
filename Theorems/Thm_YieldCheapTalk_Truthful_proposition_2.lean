import Mathlib
import Definitions.Def_YieldCheapTalk_Truthful_Setting
open MeasureTheory

namespace YieldCheapTalk.Truthful
theorem proposition_2 (M : Model) (hM : M.Standing) :
    (∃ (Q : Level → Level → ℝ) (beta : Level → Level → Level → ℝ), M.IsPBE id Q beta) ↔
      (∑ m, M.mu m .H * M.a m ≤ (1 + M.eta * (1 / M.theta .H + 1 / M.theta .L - 1)) * M.w ∧
        (1 + M.eta * (1 / M.theta .H + 1 / M.theta .L - 1)) * M.w ≤
          ∑ m, M.mu m .L * M.a m) := by sorry
end YieldCheapTalk.Truthful

