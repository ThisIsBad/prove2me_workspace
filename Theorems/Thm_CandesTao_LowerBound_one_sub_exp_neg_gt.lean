import Mathlib.Analysis.SpecialFunctions.Exp

namespace CandesTao.LowerBound

theorem one_sub_exp_neg_gt (x : ℝ) (hx : 0 < x) :
    1 - Real.exp (-x) > x - x ^ 2 / 2 := by sorry

end CandesTao.LowerBound
