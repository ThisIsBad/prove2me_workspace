import Mathlib
import Definitions.Def_CachonCoord_EffortNewsvendor_Model
import Definitions.Def_CachonCoord_EffortNewsvendor_Contracts

namespace CachonCoord.EffortNewsvendor

/-- p. 42, the display after "It can be shown with φ < 1": with a revenue sharing contract
`{w_r, φ}` and `φ < 1`, at every `q > 0` and `e > 0`,
`∂π_r(q, e, w_r, φ)/∂e < ∂Π(q, e)/∂e` (both derivatives exist). -/
theorem p42_revenue_sharing (M : Model) (wr φ q e : ℝ) (hφ : φ < 1) (hq : 0 < q) (he : 0 < e) :
    ∃ d₁ d₂ : ℝ, HasDerivAt (fun e' => M.rsRetailerProfit wr φ q e') d₁ e ∧
      HasDerivAt (fun e' => M.Pi q e') d₂ e ∧ d₁ < d₂ := by sorry

end CachonCoord.EffortNewsvendor

