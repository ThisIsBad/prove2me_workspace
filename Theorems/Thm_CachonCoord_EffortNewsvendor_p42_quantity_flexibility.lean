import Mathlib
import Definitions.Def_CachonCoord_EffortNewsvendor_Model
import Definitions.Def_CachonCoord_EffortNewsvendor_Contracts

namespace CachonCoord.EffortNewsvendor

/-- p. 42, the display after "For all δ > 0": with a quantity-flexibility contract `{w_q, δ}`,
`0 < δ ≤ 1` and wholesale price `w_q > 0`, at every `q > 0` and `e > 0`,
`∂π_r(q, e, w_q, δ)/∂e < ∂Π(q, e)/∂e` (both derivatives exist). -/
theorem p42_quantity_flexibility (M : Model) (wq δ q e : ℝ) (hwq : 0 < wq) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hq : 0 < q) (he : 0 < e) :
    ∃ d₁ d₂ : ℝ, HasDerivAt (fun e' => M.qfRetailerProfit wq δ q e') d₁ e ∧
      HasDerivAt (fun e' => M.Pi q e') d₂ e ∧ d₁ < d₂ := by sorry

end CachonCoord.EffortNewsvendor

