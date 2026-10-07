import Mathlib
import Definitions.Def_CachonCoord_EffortNewsvendor_Model
import Definitions.Def_CachonCoord_EffortNewsvendor_Contracts

namespace CachonCoord.EffortNewsvendor

/-- §6.4.1, pp. 42–43. (1) Eq. (19): with a buy back contract and `b > 0`, the retailer's
marginal profit of effort is strictly below the channel's at every `q > 0`, `e > 0`.
(2) The quantity discount `w_d` with `λ ∈ [0, 1]`, built on an effort `e° ≥ 0`: for every
`q > 0`, `π_r(q, e°) = λΠ(q, e°)` and the supplier earns `π_s(q) = (1 − λ)Π(q, e°)`; for every
`q > 0` the retailer's profit and the channel's have the same derivative in effort at every
`e > 0`, and the same maximizers over effort levels `e ≥ 0`.
(3) If `(q°, e°)`, `q° > 0`, `e° ≥ 0`, maximizes `Π` over `q ≥ 0`, `e ≥ 0`, then under `w_d` with
`λ ∈ [0, 1]` the order `q°` maximizes both `q ↦ π_r(q, e°)` and `q ↦ π_s(q)` over `q > 0`. -/
theorem sec_6_4_1_effort_coordination (M : Model) :
    (∀ wb b q e : ℝ, 0 < b → 0 < q → 0 < e →
      ∃ d₁ d₂ : ℝ, HasDerivAt (fun e' => M.bbRetailerProfit wb b q e') d₁ e ∧
        HasDerivAt (fun e' => M.Pi q e') d₂ e ∧ d₁ < d₂) ∧
    (∀ lam eo : ℝ, 0 ≤ lam → lam ≤ 1 → 0 ≤ eo →
      (∀ q : ℝ, 0 < q → M.qdRetailerProfit lam eo q eo = lam * M.Pi q eo) ∧
      (∀ q : ℝ, 0 < q → M.qdSupplierProfit lam eo q = (1 - lam) * M.Pi q eo) ∧
      (∀ q e : ℝ, 0 < q → 0 < e →
        ∃ d : ℝ, HasDerivAt (fun e' => M.qdRetailerProfit lam eo q e') d e ∧
          HasDerivAt (fun e' => M.Pi q e') d e) ∧
      (∀ q e : ℝ, 0 < q → 0 ≤ e →
        (IsMaxOn (fun e' => M.qdRetailerProfit lam eo q e') (Set.Ici 0) e ↔
          IsMaxOn (fun e' => M.Pi q e') (Set.Ici 0) e))) ∧
    (∀ lam qo eo : ℝ, 0 ≤ lam → lam ≤ 1 → 0 < qo → 0 ≤ eo →
      IsMaxOn (fun x : ℝ × ℝ => M.Pi x.1 x.2) (Set.Ici 0 ×ˢ Set.Ici 0) (qo, eo) →
      IsMaxOn (fun q => M.qdRetailerProfit lam eo q eo) (Set.Ioi 0) qo ∧
        IsMaxOn (fun q => M.qdSupplierProfit lam eo q) (Set.Ioi 0) qo) := by sorry

end CachonCoord.EffortNewsvendor

