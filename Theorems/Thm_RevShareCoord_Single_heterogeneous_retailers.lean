import Mathlib
import Definitions.Def_RevShareCoord_Single_Model

namespace RevShareCoord.Single

/-- Sec. 2.2, p. 7: the coordinating revenue-sharing contract is independent of the marginal
revenue curve. For a unit cost `c` and a revenue share `φ ∈ (0, 1]` there is one wholesale
price `w` such that every retailer, whatever his revenue function `R` (any model with unit
cost `c`), orders his own integrated-channel quantity `q_I` as his unique optimum. -/
theorem heterogeneous_retailers (c φ : ℝ) (hφ0 : 0 < φ) (hφ1 : φ ≤ 1) :
    ∃ w : ℝ, 0 ≤ w ∧ ∀ M : Model, M.c = c → ∀ qI : ℝ, 0 ≤ qI →
      IsMaxOn M.Pi (Set.Ici 0) qI →
      IsMaxOn (M.retailerProfit φ w) (Set.Ici 0) qI ∧
        ∀ q : ℝ, 0 ≤ q → IsMaxOn (M.retailerProfit φ w) (Set.Ici 0) q → q = qI := by sorry

end RevShareCoord.Single

