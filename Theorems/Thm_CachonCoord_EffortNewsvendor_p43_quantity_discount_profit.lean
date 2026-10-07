import Mathlib
import Definitions.Def_CachonCoord_EffortNewsvendor_Model
import Definitions.Def_CachonCoord_EffortNewsvendor_Contracts

namespace CachonCoord.EffortNewsvendor

/-- p. 43, the two displays of `π_r`: under the quantity discount `w_d` with `λ ∈ [0, 1]`, for
every `q > 0` and every effort `e`,
`π_r(q, e) = pS(q, e) − (1 − λ)pS(q, e°) − λcq − g(e) + (1 − λ)g(e°)`, and at `e = e°`,
`π_r(q, e°) = λpS(q, e°) − λcq − λg(e°) = λΠ(q, e°)`. -/
theorem p43_quantity_discount_profit (M : Model) (lam eo q e : ℝ) (hlam0 : 0 ≤ lam)
    (hlam1 : lam ≤ 1) (hq : 0 < q) :
    M.qdRetailerProfit lam eo q e =
        M.p * M.S q e - (1 - lam) * M.p * M.S q eo - lam * M.c * q - M.effortCost e
          + (1 - lam) * M.effortCost eo ∧
      M.qdRetailerProfit lam eo q eo =
        lam * M.p * M.S q eo - lam * M.c * q - lam * M.effortCost eo ∧
      M.qdRetailerProfit lam eo q eo = lam * M.Pi q eo := by sorry

end CachonCoord.EffortNewsvendor

