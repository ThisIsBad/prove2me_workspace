import Mathlib
import Definitions.Def_YieldCheapTalk_Truthful_Setting
open MeasureTheory

namespace YieldCheapTalk.Truthful
theorem ic_condition_5 (M : Model) (hM : M.Standing) :
    (∀ (Q : Level → Level → ℝ) (beta : Level → Level → Level → ℝ), M.IsPBE id Q beta →
        ∀ t m, Q t m = M.Qr (M.theta t) (M.a m)) ∧
      ((∃ (Q : Level → Level → ℝ) (beta : Level → Level → Level → ℝ), M.IsPBE id Q beta) ↔
        M.IC5) := by sorry
end YieldCheapTalk.Truthful

