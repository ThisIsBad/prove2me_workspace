import Mathlib
import Definitions.Def_RevShareCoord_Competing_Game
import Definitions.Def_RevShareCoord_Competing_Cournot

namespace RevShareCoord.Competing

/-- **Sec. 4.1.2, the supplier's optimal wholesale price (pp. 19–20).** Cournot revenues (7) with
`0 ≤ β < 1`, `n ≥ 1` symmetric retailers, unit cost `0 < c < 1`, a common wholesale price and no
revenue sharing. Let `w* = (1 + c)/2`.
1. The symmetric profile `q_i^N(w*) = (1 − w*)/(2 + β(n − 1))` is a Nash equilibrium at `w*`.
2. For every price `w > 0` and every Nash equilibrium `q̄` at `w`, the supplier's profit
   `Σᵢ (w − c) qᵢ` is at most her profit at `w*` with `q̄^N(w*)`, and strictly less if `w ≠ w*`.
3. The gap `w* − w^I` equals `(1 − c)/(2 + 2β(n − 1))`. -/
theorem cournot_supplier_optimal_price {n : ℕ} (β c : ℝ) (hn : 1 ≤ n) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hc0 : 0 < c) (hc1 : c < 1) :
    IsNashEquilibrium (cournotRevenue β) 1 (fun _ : Fin n => (1 + c) / 2)
        (fun _ => cournotQN β n ((1 + c) / 2)) ∧
      (∀ w : ℝ, 0 < w → ∀ q : Fin n → ℝ,
        IsNashEquilibrium (cournotRevenue β) 1 (fun _ => w) q →
          supplierProfit (cournotRevenue β) c 1 (fun _ => w) q ≤
              supplierProfit (cournotRevenue β) c 1 (fun _ : Fin n => (1 + c) / 2)
                (fun _ => cournotQN β n ((1 + c) / 2)) ∧
            (w ≠ (1 + c) / 2 →
              supplierProfit (cournotRevenue β) c 1 (fun _ => w) q <
                supplierProfit (cournotRevenue β) c 1 (fun _ : Fin n => (1 + c) / 2)
                  (fun _ => cournotQN β n ((1 + c) / 2)))) ∧
      (1 + c) / 2 - cournotWI β n c = (1 - c) / (2 + 2 * β * ((n : ℝ) - 1)) := by sorry

end RevShareCoord.Competing

