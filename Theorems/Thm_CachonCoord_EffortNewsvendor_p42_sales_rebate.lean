import Mathlib
import Definitions.Def_CachonCoord_EffortNewsvendor_Model
import Definitions.Def_CachonCoord_EffortNewsvendor_Contracts

namespace CachonCoord.EffortNewsvendor

/-- pp. 42–43, the display after "for r > 0 and q > t": with a sales rebate contract
`{w_s, r, t}`, `r > 0` and threshold `t ≥ 0`, at every `q > t` and `e > 0`,
`∂π_r(q, e, w_s, r, t)/∂e > ∂Π(q, e)/∂e` (both derivatives exist). -/
theorem p42_sales_rebate (M : Model) (ws r t q e : ℝ) (hr : 0 < r) (ht : 0 ≤ t) (hqt : t < q)
    (he : 0 < e) :
    ∃ d₁ d₂ : ℝ, HasDerivAt (fun e' => M.srRetailerProfit ws r t q e') d₁ e ∧
      HasDerivAt (fun e' => M.Pi q e') d₂ e ∧ d₂ < d₁ := by sorry

end CachonCoord.EffortNewsvendor

