import Mathlib
import Definitions.Def_BellmanTheoryDP_GoldMining_Model

namespace BellmanTheoryDP.GoldMining

/-- Bellman (1954), Eq. (8.2): the optimal return `f(x, y)` of the two-mine problem satisfies
`f(x, y) = max (p [r x + f((1-r) x, y)]) (q [s y + f(x, (1-s) y)])`. -/
theorem optimal_return_functional_equation (p q r s x y : ℝ)
    (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) (hq1 : q < 1)
    (hr0 : 0 < r) (hr1 : r < 1) (hs0 : 0 < s) (hs1 : s < 1)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    optimalReturn p q r s x y =
      max (p * (r * x + optimalReturn p q r s ((1 - r) * x) y))
          (q * (s * y + optimalReturn p q r s x ((1 - s) * y))) := by sorry

end BellmanTheoryDP.GoldMining

