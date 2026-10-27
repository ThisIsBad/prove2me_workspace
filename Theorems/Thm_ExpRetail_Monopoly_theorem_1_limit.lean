import Mathlib
import Definitions.Def_ExpRetail_Monopoly_Model

namespace ExpRetail.Monopoly

theorem theorem_1_limit (P : Params) (hP : P.Standing) :
    Filter.Tendsto (optProfit P) Filter.atTop Filter.atBot ∧ 0 < optProfitN P := by sorry

end ExpRetail.Monopoly

