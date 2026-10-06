import Mathlib
import Definitions.Def_RevShareCoord_Competing_Game
import Definitions.Def_RevShareCoord_Competing_Cournot

namespace RevShareCoord.Competing

open Finset

/-- **Sec. 4.1.2, the integrated quantities and the coordinating price (p. 19).** Cournot
revenues (7), `Rᵢ(q̄) = qᵢ(1 − qᵢ − β Σ_{j≠i} qⱼ)`, with `0 ≤ β < 1` and unit cost `0 < c < 1`.
1. The symmetric profile `q_i^I = (1 − c)/(2 + 2β(n − 1))` maximizes the system profit
   `Π(q̄) = Σᵢ Rᵢ(q̄) − c Σᵢ qᵢ` over `q̄ ≥ 0`, and is its only maximizer there.
2. `R_j^i(q̄) = ∂R_j/∂q_i (q̄) = −β q_j` for all `j ≠ i` and every profile `q̄`.
3. The coordinating price `c − Σ_{j≠i} R_j^i(q̄^I)` equals
   `w^I = c + β(n − 1)(1 − c)/(2 + 2β(n − 1))` for every `i`.
4. At the common wholesale price `w^I` (no revenue sharing) the profile `q̄^I` is a Nash
   equilibrium. -/
theorem cournot_coordinating_price {n : ℕ} (β c : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hc0 : 0 < c) (hc1 : c < 1) :
    (IsMaxOn (systemProfit (cournotRevenue β) c) {q : Fin n → ℝ | ∀ i, 0 ≤ q i}
        (fun _ => cournotQI β n c) ∧
      ∀ q ∈ {q : Fin n → ℝ | ∀ i, 0 ≤ q i},
        IsMaxOn (systemProfit (cournotRevenue β) c) {q : Fin n → ℝ | ∀ i, 0 ≤ q i} q →
          q = fun _ => cournotQI β n c) ∧
    (∀ (q : Fin n → ℝ) (i j : Fin n), j ≠ i →
      HasDerivAt (fun t => cournotRevenue β j (Function.update q i t)) (-β * q j) (q i)) ∧
    (∀ i : Fin n, c - ∑ j ∈ univ.erase i, (-β * cournotQI β n c) = cournotWI β n c) ∧
    IsNashEquilibrium (cournotRevenue β) 1 (fun _ : Fin n => cournotWI β n c)
      (fun _ => cournotQI β n c) := by sorry

end RevShareCoord.Competing

