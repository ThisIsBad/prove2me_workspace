import Mathlib
import Definitions.Def_CachonCoord_InternalMarket_Revenue
import Definitions.Def_CachonCoord_InternalMarket_Model

namespace CachonCoord.InternalMarket

open MeasureTheory

/-- §6.9.1, pp. 93–94 (Cachon 2003, 3rd draft), the internal market coordinates the chain.
1. **The market.** For every realization `α₁, α₂ > 0` and output `Q > 0`, at the price `w(α, Q)`
   retailer one's unique optimal quantity is `γ°(α) Q` and retailer two's is `(1 − γ°(α)) Q` (so they
   order exactly `Q` in total), this allocation maximizes total retailer revenue over all
   `q₁, q₂ ≥ 0` with `q₁ + q₂ ≤ Q`, and `∂π(α, Q)/∂Q = w(α, Q)`.
2. **The manager.** If `K = E[(A₁^η + A₂^η)^{1/η} Y^{(η−1)/η}]` is integrable, `E[Y] > 0` and `e° > 0`
   satisfies (45), then under the per-unit payment (46) the manager's expected utility
   `u(e) = payRate(e°) E[Ye] − c(e)` is uniquely maximized over `[0, ∞)` at `e°`, the payment rate
   equals `E[Q w(A, Q) | e°] / E[Q | e°]`, and the supplier's expected profit from the market,
   `E[Q w(A, Q) | e°] − payRate(e°) E[Q | e°]`, is zero. -/
theorem sec_6_9_1_internal_market {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) :
    (∀ α₁ α₂ Q : ℝ, 0 < α₁ → 0 < α₂ → 0 < Q →
      (∀ q : ℝ, 0 ≤ q →
        (IsMaxOn (retailerProfit M.η α₁ (price M.η α₁ α₂ Q)) (Set.Ici 0) q ↔
          q = optShare M.η α₁ α₂ * Q)) ∧
      (∀ q : ℝ, 0 ≤ q →
        (IsMaxOn (retailerProfit M.η α₂ (price M.η α₁ α₂ Q)) (Set.Ici 0) q ↔
          q = (1 - optShare M.η α₁ α₂) * Q)) ∧
      (∀ q₁ q₂ : ℝ, 0 ≤ q₁ → 0 ≤ q₂ → q₁ + q₂ ≤ Q →
        α₁ * q₁ ^ ((M.η - 1) / M.η) + α₂ * q₂ ^ ((M.η - 1) / M.η) ≤
          α₁ * (optShare M.η α₁ α₂ * Q) ^ ((M.η - 1) / M.η) +
            α₂ * ((1 - optShare M.η α₁ α₂) * Q) ^ ((M.η - 1) / M.η)) ∧
      HasDerivAt (fun Q' => optRevenue M.η α₁ α₂ Q') (price M.η α₁ α₂ Q) Q) ∧
    (Integrable (fun ω => (M.A₁ ω ^ M.η + M.A₂ ω ^ M.η) ^ (1 / M.η) *
        M.Y ω ^ ((M.η - 1) / M.η)) M.P →
      0 < ∫ ω, M.Y ω ∂M.P →
      ∀ eo : ℝ, 0 < eo →
        (M.η - 1) / M.η * eo ^ (-1 / M.η) * M.K - M.c' eo = 0 →
        IsMaxOn (M.managerUtility eo) (Set.Ici 0) eo ∧
        (∀ e : ℝ, 0 ≤ e → IsMaxOn (M.managerUtility eo) (Set.Ici 0) e → e = eo) ∧
        M.payRate eo = M.expMarketRevenue eo / M.expOutput eo ∧
        M.expMarketRevenue eo - M.payRate eo * M.expOutput eo = 0) := by sorry

end CachonCoord.InternalMarket

