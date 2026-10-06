import Mathlib
import Definitions.Def_RevShareCoord_Competing_Game
import Definitions.Def_RevShareCoord_Competing_Model

namespace RevShareCoord.Competing

open Finset

/-- **Sec. 3.2, Eq. (8) and marginal-cost pricing (p. 13).** Index convention:
`M.dR i j q = R_j^i(q̄) = ∂R_j/∂q_i`.

1. Under wholesale prices `w̄` (`φ = 1`), every Nash equilibrium `q̄^N` with all entries positive
   satisfies `R_i^i(q̄^N) = wᵢ` for every `i` (Eq. (8)).
2. Let `q̄^I` have positive entries and solve (6). If location `i` imposes a negative externality
   at `q̄^I`, `Σ_{j≠i} R_j^i(q̄^I) < 0`, then `R_i^i(q̄^I) > c`, and `q̄^I` is not a Nash equilibrium
   when the supplier charges every retailer the marginal cost `c`. -/
theorem wholesale_foc_marginal_cost {n : ℕ} (M : Model n) :
    (∀ (w : Fin n → ℝ) (qN : Fin n → ℝ), (∀ i, 0 < w i) →
        IsNashEquilibrium M.R 1 w qN → (∀ i, 0 < qN i) → ∀ i, M.dR i i qN = w i) ∧
    (∀ qI : Fin n → ℝ, (∀ i, 0 < qI i) → M.FOC qI →
        ∀ i, ∑ j ∈ univ.erase i, M.dR i j qI < 0 →
          M.c < M.dR i i qI ∧ ¬ IsNashEquilibrium M.R 1 (fun _ => M.c) qI) := by sorry

end RevShareCoord.Competing

