import Mathlib
import Definitions.Def_CachonCoord_Proportional_Demand

namespace CachonCoord.Proportional

/-- Eq. (20), p. 50: the integrated supply chain faces a single newsvendor problem, whose
optimal order quantity `q°` is defined by `F(q°) = (p − c)/p`. Such a `q° > 0` exists, and a
quantity `q ≥ 0` maximizes the chain profit `Π(q) = pS(q) − cq` over `q ≥ 0` exactly when
`F(q) = (p − c)/p`. -/
theorem eq_20 (M : Model) :
    (∃ qo : ℝ, 0 < qo ∧ M.F qo = (M.p - M.c) / M.p) ∧
      ∀ q : ℝ, 0 ≤ q →
        (IsMaxOn M.chainProfit (Set.Ici 0) q ↔ M.F q = (M.p - M.c) / M.p) := by sorry

end CachonCoord.Proportional

