import Mathlib
import Definitions.Def_RevShareCoord_Competing_Game
import Definitions.Def_RevShareCoord_Competing_Model

namespace RevShareCoord.Competing

open Finset

/-- **Sec. 3.2, `w_i^I` above marginal cost (p. 13).** Index convention:
`M.dR i j q = R_j^i(q̄) = ∂R_j/∂q_i`. If `R_j^i(q̄^I) ≤ 0` for all `j ≠ i` (raising the quantity at
one location does not raise revenue at another), then `w_i^I = c − Σ_{j≠i} R_j^i(q̄^I) ≥ c` for
every `i`, with strict inequality for every `i` such that `R_j^i(q̄^I) < 0` for some `j ≠ i`. -/
theorem wI_above_cost {n : ℕ} (M : Model n) (qI : Fin n → ℝ)
    (hsub : ∀ i j, j ≠ i → M.dR i j qI ≤ 0) :
    (∀ i, M.c ≤ M.wI qI i) ∧
      ∀ i, (∃ j, j ≠ i ∧ M.dR i j qI < 0) → M.c < M.wI qI i := by sorry

end RevShareCoord.Competing

