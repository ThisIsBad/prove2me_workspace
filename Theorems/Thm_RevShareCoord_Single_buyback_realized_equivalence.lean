import Mathlib
import Definitions.Def_RevShareCoord_Single_Newsvendor

namespace RevShareCoord.Single

/-- Sec. 2.3, p. 9: with `b* = p(1 − φ)` and `w_b* = p(1 − φ) + φc`, the buy-back contract
`{b*, w_b*}` and the revenue-sharing contract `{φ, φc}` give the retailer the same realized profit,
and the supplier the same realized profit, for every order quantity `q` and every realization `D`
of demand. -/
theorem buyback_realized_equivalence (p c φ q D : ℝ) :
    bbRetailerRealized p (p * (1 - φ)) (p * (1 - φ) + φ * c) q D =
        rsRetailerRealized p φ (φ * c) q D ∧
      bbSupplierRealized (p * (1 - φ)) (p * (1 - φ) + φ * c) c q D =
        rsSupplierRealized p φ (φ * c) c q D := by sorry

end RevShareCoord.Single

