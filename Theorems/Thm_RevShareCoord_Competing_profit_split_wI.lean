import Mathlib
import Definitions.Def_RevShareCoord_Competing_Game
import Definitions.Def_RevShareCoord_Competing_Model

namespace RevShareCoord.Competing

open Finset

/-- **Sec. 3.2, the division of profits under `w̄^I` (p. 14).** Index convention:
`M.dR i j q = R_j^i(q̄) = ∂R_j/∂q_i`. Under the wholesale prices `w_i^I = c − Σ_{j≠i} R_j^i(q̄^I)`
(`φ = 1`), at the profile `q̄^I` the supplier earns
`π_s(q̄^I, w̄^I) = Σᵢ q_i^I Σ_{j≠i} (−R_j^i(q̄^I))`, and retailer `i` earns
`π_{rᵢ}(q̄^I, w̄^I) = Rᵢ(q̄^I) − q_i^I w_i^I`. -/
theorem profit_split_wI {n : ℕ} (M : Model n) (qI : Fin n → ℝ) :
    supplierProfit M.R M.c 1 (M.wI qI) qI =
        ∑ i, qI i * ∑ j ∈ univ.erase i, (-M.dR i j qI) ∧
      ∀ i, retailerProfit M.R 1 (M.wI qI) qI i = M.R i qI - qI i * M.wI qI i := by sorry

end RevShareCoord.Competing

