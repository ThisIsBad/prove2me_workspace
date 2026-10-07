import Mathlib
import Definitions.Def_CachonCoord_Proportional_Demand
import Definitions.Def_CachonCoord_Proportional_Nash
import Definitions.Def_CachonCoord_Proportional_Game

namespace CachonCoord.Proportional

/-- p. 51: "when `b < w < p` … in this game there exists a unique Nash equilibrium in which the
total order quantity, `q*`, is implicitly given by (22) and each retailer's order quantity equals
`q*_i = q*/n`." There is `q* > 0` solving (22), and a profile is a Nash equilibrium if and only
if every retailer orders `q*/n`. -/
theorem unique_nash (M : Model) (n : ℕ) (hn : 2 ≤ n) (w b : ℝ) (hbw : b < w) (hwp : w < M.p) :
    ∃ qs : ℝ, 0 < qs ∧ M.lhs22 n qs = (M.p - w) / (M.p - b) ∧
      ∀ q : Fin n → ℝ, M.IsNashEq w b q ↔ ∀ i, q i = qs / n := by sorry

end CachonCoord.Proportional

