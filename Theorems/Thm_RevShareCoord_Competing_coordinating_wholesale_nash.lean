import Mathlib
import Definitions.Def_RevShareCoord_Competing_Game
import Definitions.Def_RevShareCoord_Competing_Model

namespace RevShareCoord.Competing

open Finset

/-- **Sec. 3.2, the coordinating wholesale prices (p. 13).** Index convention:
`M.dR i j q = R_j^i(q̄) = ∂R_j/∂q_i`. Let `q̄^I` have positive entries and solve the first-order
system (6), `R_i^i(q̄^I) + Σ_{j≠i} R_j^i(q̄^I) = c`. If the supplier charges retailer `i` the
wholesale price `w_i^I = c − Σ_{j≠i} R_j^i(q̄^I)` (no revenue sharing, `φ = 1`), then `q̄^I` is a
Nash equilibrium of the retailers' quantity game. -/
theorem coordinating_wholesale_nash {n : ℕ} (M : Model n) (qI : Fin n → ℝ)
    (hpos : ∀ i, 0 < qI i) (hfoc : M.FOC qI) :
    IsNashEquilibrium M.R 1 (M.wI qI) qI := by sorry

end RevShareCoord.Competing

