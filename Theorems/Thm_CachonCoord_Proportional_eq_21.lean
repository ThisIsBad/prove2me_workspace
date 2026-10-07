import Mathlib
import Definitions.Def_CachonCoord_Proportional_Demand
import Definitions.Def_CachonCoord_Proportional_Nash
import Definitions.Def_CachonCoord_Proportional_Game

namespace CachonCoord.Proportional

/-- p. 51, the first order condition and Eq. (21): when `b < w < p`, at any Nash equilibrium
`q*` of the `n`-retailer game every retailer orders a positive amount, satisfies the first order
condition `∂π_i/∂q_i = 0`, i.e. (in the page's scaling)
`q* (p − w)/(p − b) − q*_i F(q*) − q*_{−i} (1/q*) ∫_0^{q*} F = 0`, and hence
`q*_i = q* ((p − w)/(p − b) − (1/q*) ∫_0^{q*} F) / (F(q*) − (1/q*) ∫_0^{q*} F)`, where
`q* = ∑_j q*_j` and `q*_{−i} = q* − q*_i`. -/
theorem eq_21 (M : Model) (n : ℕ) (hn : 2 ≤ n) (w b : ℝ) (hbw : b < w) (hwp : w < M.p)
    (q : Fin n → ℝ) (hq : M.IsNashEq w b q) (i : Fin n) :
    0 < q i ∧
      HasDerivAt (fun y => M.retailerProfit w b y (Model.total q - q i)) 0 (q i) ∧
      Model.total q * ((M.p - w) / (M.p - b)) - q i * M.F (Model.total q) -
          (Model.total q - q i) * M.avgF (Model.total q) = 0 ∧
      q i = Model.total q * ((M.p - w) / (M.p - b) - M.avgF (Model.total q)) /
          (M.F (Model.total q) - M.avgF (Model.total q)) := by sorry

end CachonCoord.Proportional

