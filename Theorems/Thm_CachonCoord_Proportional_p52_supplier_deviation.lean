import Mathlib
import Definitions.Def_CachonCoord_Proportional_Demand
import Definitions.Def_CachonCoord_Proportional_Nash
import Definitions.Def_CachonCoord_Proportional_Game

namespace CachonCoord.Proportional

/-- p. 52: with the wholesale price contract the supplier earns `π_s(q, ŵ(q)) = q (ŵ(q) − c)`;
"Assuming `n > 1`, differentiate `π_s(q, ŵ(q))` with respect to `q` and evaluate at `ŵ(q°)`, the
coordinating wholesale price, `∂π_s(q°, ŵ(q°))/∂q = −q° p f(q°)/n < 0`." The negativity needs
`f(q°) > 0`, assumed here. -/
theorem p52_supplier_deviation (M : Model) (n : ℕ) (hn : 2 ≤ n) (qo : ℝ)
    (hqo : M.F qo = (M.p - M.c) / M.p) (hf : 0 < M.density qo) :
    HasDerivAt (fun q => M.supplierProfit (M.what n q) 0 q)
        (-(qo * M.p * M.density qo) / n) qo ∧
      -(qo * M.p * M.density qo) / n < 0 := by sorry

end CachonCoord.Proportional

