import Mathlib
import Definitions.Def_RevShareCoord_Single_Model

namespace RevShareCoord.Single

/-- Sec. 2.2, p. 6 (goal): let `q_I` be the integrated channel's optimal order quantity and let
`φ ∈ (0, 1]`. Under the revenue-sharing contract `{φ, w(φ)}` with `w(φ) = φc`:
(1) `q_I` is the retailer's unique optimal order quantity; (2) `w(φ) ≤ c`;
(3) `π_r(q_I) = φΠ(q_I)`; (4) `π_s(q_I, w(φ), φ) = (1 − φ)Π(q_I)`. -/
theorem revenue_sharing_coordinates (M : Model) (φ : ℝ) (hφ0 : 0 < φ) (hφ1 : φ ≤ 1)
    (qI : ℝ) (hqI0 : 0 ≤ qI) (hqI : IsMaxOn M.Pi (Set.Ici 0) qI) :
    (IsMaxOn (M.retailerProfit φ (φ * M.c)) (Set.Ici 0) qI ∧
      ∀ q : ℝ, 0 ≤ q → IsMaxOn (M.retailerProfit φ (φ * M.c)) (Set.Ici 0) q → q = qI) ∧
    φ * M.c ≤ M.c ∧
    M.retailerProfit φ (φ * M.c) qI = φ * M.Pi qI ∧
    M.supplierProfit φ (φ * M.c) qI = (1 - φ) * M.Pi qI := by sorry

end RevShareCoord.Single

