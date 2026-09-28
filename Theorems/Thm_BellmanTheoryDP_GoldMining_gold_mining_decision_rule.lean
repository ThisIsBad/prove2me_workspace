import Mathlib
import Definitions.Def_BellmanTheoryDP_GoldMining_Model

namespace BellmanTheoryDP.GoldMining

/-- Bellman (1954), Eq. (8.3), with the printed denominators `(1 - r)`, `(1 - s)` corrected to
`(1 - p)`, `(1 - q)`: comparing the two branches of (8.2),
`V_A = p [r x + f((1-r) x, y)]` and `V_B = q [s y + f(x, (1-s) y)]`,
(a) if `p r x / (1 - p) > q s y / (1 - q)` then `V_A > V_B` (choose A);
(b) if `p r x / (1 - p) < q s y / (1 - q)` then `V_A < V_B` (choose B);
(c) if `p r x / (1 - p) = q s y / (1 - q)` then `V_A = V_B` (choose either). -/
theorem gold_mining_decision_rule (p q r s x y : ℝ)
    (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) (hq1 : q < 1)
    (hr0 : 0 < r) (hr1 : r < 1) (hs0 : 0 < s) (hs1 : s < 1)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (q * s * y / (1 - q) < p * r * x / (1 - p) →
        q * (s * y + optimalReturn p q r s x ((1 - s) * y)) <
          p * (r * x + optimalReturn p q r s ((1 - r) * x) y)) ∧
    (p * r * x / (1 - p) < q * s * y / (1 - q) →
        p * (r * x + optimalReturn p q r s ((1 - r) * x) y) <
          q * (s * y + optimalReturn p q r s x ((1 - s) * y))) ∧
    (p * r * x / (1 - p) = q * s * y / (1 - q) →
        p * (r * x + optimalReturn p q r s ((1 - r) * x) y) =
          q * (s * y + optimalReturn p q r s x ((1 - s) * y))) := by sorry

end BellmanTheoryDP.GoldMining

