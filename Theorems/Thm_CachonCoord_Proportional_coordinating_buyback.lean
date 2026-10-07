import Mathlib
import Definitions.Def_CachonCoord_Proportional_Demand
import Definitions.Def_CachonCoord_Proportional_Nash
import Definitions.Def_CachonCoord_Proportional_Game

namespace CachonCoord.Proportional

/-- §6.5.1, pp. 51–53, the coordinating buy-back contract. Let `n ≥ 2`, `b < p`, and let `q°`
solve (20), `F(q°) = (p − c)/p`; let `w = w_b(b)` (p. 52). Then `q°` maximizes the chain profit,
`b < w < p`, the profile in which every retailer orders `q°/n` is the unique Nash equilibrium,
each retailer earns `((p − b)/(pn²)) Π(q°)` there, and the supplier, who receives `w q°`, pays
`c q°` in production and `b` per unit returned, earns `((p(n − 1) + b)/(pn)) Π(q°)`. -/
theorem coordinating_buyback (M : Model) (n : ℕ) (hn : 2 ≤ n) (b qo : ℝ) (hb : b < M.p)
    (hqo : M.F qo = (M.p - M.c) / M.p) :
    IsMaxOn M.chainProfit (Set.Ici 0) qo ∧
      b < M.wb n b qo ∧ M.wb n b qo < M.p ∧
      (∀ q : Fin n → ℝ, M.IsNashEq (M.wb n b qo) b q ↔ ∀ i, q i = qo / n) ∧
      (∀ i : Fin n, M.payoff (M.wb n b qo) b i (fun _ => qo / n) =
        (M.p - b) / (M.p * (n : ℝ) ^ 2) * M.chainProfit qo) ∧
      M.supplierProfit (M.wb n b qo) b qo =
        (M.p * ((n : ℝ) - 1) + b) / (M.p * n) * M.chainProfit qo := by sorry

end CachonCoord.Proportional

