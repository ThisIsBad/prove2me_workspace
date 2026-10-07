import Mathlib
import Definitions.Def_CachonCoord_Proportional_Demand
import Definitions.Def_CachonCoord_Proportional_Nash
import Definitions.Def_CachonCoord_Proportional_Game

namespace CachonCoord.Proportional

/-- p. 51–52: `ŵ(q)` is "the wholesale price that induces the retailers to order `q` units with a
wholesale price contract (i.e., with `b = 0`). From (22),
`ŵ(q) = p (1 − (1/n) F(q) − ((n − 1)/n) (1/q) ∫_0^q F(x) dx)`." For every `q > 0`, under the
wholesale price contract `w = ŵ(q)`, `b = 0`, a profile is a Nash equilibrium if and only if every
retailer orders `q/n`. -/
theorem p52_what_induces (M : Model) (n : ℕ) (hn : 2 ≤ n) (q : ℝ) (hq : 0 < q) :
    ∀ r : Fin n → ℝ, M.IsNashEq (M.what n q) 0 r ↔ ∀ i, r i = q / n := by sorry

end CachonCoord.Proportional

