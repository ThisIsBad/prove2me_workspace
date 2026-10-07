import Mathlib
import Definitions.Def_CachonCoord_Proportional_Demand
import Definitions.Def_CachonCoord_Proportional_Nash
import Definitions.Def_CachonCoord_Proportional_Game

namespace CachonCoord.Proportional

/-- p. 52: with `F(q°) = (p − c)/p` (the page prints `(p − c)/c`) and `(1/q)∫_0^q F < F(q)`,
"it can be shown that `ŵ(q°) > c` when `n > 1`. Hence, the supplier earns a positive profit with
that coordinating contract." -/
theorem p52_what_above_cost (M : Model) (n : ℕ) (hn : 2 ≤ n) (qo : ℝ)
    (hqo : M.F qo = (M.p - M.c) / M.p) :
    M.c < M.what n qo ∧ 0 < M.supplierProfit (M.what n qo) 0 qo := by sorry

end CachonCoord.Proportional

