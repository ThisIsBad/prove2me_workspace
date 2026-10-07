import Mathlib
import Definitions.Def_CachonCoord_EffortNewsvendor_Model
import Definitions.Def_CachonCoord_EffortNewsvendor_Contracts

namespace CachonCoord.EffortNewsvendor

/-- Eq. (19), p. 42: with a buy back contract `{w_b, b}` and `b > 0`, at every order
quantity `q > 0` and effort `e > 0` the retailer's marginal profit of effort is strictly below
the channel's: `∂π_r(q, e, w_b, b)/∂e < ∂Π(q, e)/∂e` (both derivatives exist). -/
theorem eq_19 (M : Model) (wb b q e : ℝ) (hb : 0 < b) (hq : 0 < q) (he : 0 < e) :
    ∃ d₁ d₂ : ℝ, HasDerivAt (fun e' => M.bbRetailerProfit wb b q e') d₁ e ∧
      HasDerivAt (fun e' => M.Pi q e') d₂ e ∧ d₁ < d₂ := by sorry

end CachonCoord.EffortNewsvendor

