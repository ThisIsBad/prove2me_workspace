import Mathlib
import Definitions.Def_CachonCoord_Proportional_Demand
import Definitions.Def_CachonCoord_Proportional_Nash
import Definitions.Def_CachonCoord_Proportional_Game

namespace CachonCoord.Proportional

/-- p. 51: "The left hand side of (22) is decreasing in `n`. Hence, `q*` is increasing in `n`
for fixed contractual terms: a single retailer that faces market demand `D` purchases less than
multiple retailers facing the same demand." For `1 ≤ m < n`: `L_n(q) < L_m(q)` for every
`q > 0`, and for `b < w < p` the root of (22) with `m` retailers is strictly below the root
with `n` retailers. -/
theorem p51_increasing_in_n (M : Model) (m n : ℕ) (hm : 1 ≤ m) (hmn : m < n) :
    (∀ q : ℝ, 0 < q → M.lhs22 n q < M.lhs22 m q) ∧
      ∀ w b : ℝ, b < w → w < M.p → ∀ qm qn : ℝ, 0 < qm → 0 < qn →
        M.lhs22 m qm = (M.p - w) / (M.p - b) → M.lhs22 n qn = (M.p - w) / (M.p - b) →
        qm < qn := by sorry

end CachonCoord.Proportional

