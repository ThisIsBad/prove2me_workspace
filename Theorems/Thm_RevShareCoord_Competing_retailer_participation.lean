import Mathlib
import Definitions.Def_RevShareCoord_Competing_Game
import Definitions.Def_RevShareCoord_Competing_Model

namespace RevShareCoord.Competing

open Finset

/-- **Sec. 3.2, participation under `w̄^I` (p. 14).** Index convention:
`M.dR i j q = R_j^i(q̄) = ∂R_j/∂q_i`. Let `q̄^I` have positive entries and solve (6). Assume that a
location stocking nothing earns nonnegative revenue: `Rᵢ(q̄^I with qᵢ replaced by 0) ≥ 0`. Then
every retailer earns a nonnegative profit under the wholesale prices `w̄^I`:
`π_{rᵢ}(q̄^I, w̄^I) = Rᵢ(q̄^I) − q_i^I w_i^I ≥ 0`. -/
theorem retailer_participation {n : ℕ} (M : Model n) (qI : Fin n → ℝ)
    (hpos : ∀ i, 0 < qI i) (hfoc : M.FOC qI)
    (hzero : ∀ i, 0 ≤ M.R i (Function.update qI i 0)) :
    ∀ i, 0 ≤ retailerProfit M.R 1 (M.wI qI) qI i := by sorry

end RevShareCoord.Competing

