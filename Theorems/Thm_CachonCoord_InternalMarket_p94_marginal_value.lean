import Mathlib
import Definitions.Def_CachonCoord_InternalMarket_Revenue

namespace CachonCoord.InternalMarket

/-- §6.9.1, p. 94 (Cachon 2003, 3rd draft): `w(α, Q)` is the marginal value of additional
production, `∂π(α, Q)/∂Q = w(α, Q)`, for `α₁, α₂ > 0`, `η > 1`, `Q > 0`. -/
theorem p94_marginal_value (η α₁ α₂ Q : ℝ) (hη : 1 < η) (hα₁ : 0 < α₁) (hα₂ : 0 < α₂)
    (hQ : 0 < Q) :
    HasDerivAt (fun Q' => optRevenue η α₁ α₂ Q') (price η α₁ α₂ Q) Q := by sorry

end CachonCoord.InternalMarket

