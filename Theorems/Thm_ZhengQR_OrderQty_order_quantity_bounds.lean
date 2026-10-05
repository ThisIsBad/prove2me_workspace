import Mathlib
import Definitions.Def_ZhengQR_OrderQty_newsvendorCost
import Definitions.Def_ZhengQR_OrderQty_qrMachinery

open MeasureTheory Filter Topology

namespace ZhengQR.OrderQty

/-- Theorem 2 (Zheng 1992, p. 96). With `Q̄`, `Q̄₁`, `Q̄₂` the positive solutions of
`Q H₀(Q) = 2λK`, `H₀(Q) = H_d(Q*_d)` and `∫_0^Q H₀(y) dy = λK`:
(a) each of the three equations has exactly one positive solution, and for every optimal order
quantity `Q*`, `Q*_d ≤ Q* ≤ Q̄`, `Q̄ ≤ Q̄₁`, `Q̄ ≤ Q̄₂`;
(b) with `λ, L, h, p, μ` fixed, `K ↦ Q̄₁(K) - Q*_d(K)` is nondecreasing on `(0, ∞)` ("increasing")
and converges to a finite constant as `K → ∞`. -/
theorem order_quantity_bounds
    {lam L h p : ℝ} {μ : Measure ℝ}
    (hlam : 0 < lam) (hL : 0 < L) (hh : 0 < h) (hp : 0 < p)
    (hμ : IsLeadtimeDemand lam L μ)
    (hG : ∃! y : ℝ, IsMinimizer (newsvendorCost h p μ) y) :
    (∀ K : ℝ, 0 < K →
      (∃! Q : ℝ, 0 < Q ∧ Q * H0fun (newsvendorCost h p μ) Q = 2 * lam * K) ∧
      (∃! Q : ℝ, 0 < Q ∧
        H0fun (newsvendorCost h p μ) Q = Hfun (eoqCost lam L h p) (eoqQty lam K h p)) ∧
      (∃! Q : ℝ, 0 < Q ∧ (∫ y in (0 : ℝ)..Q, H0fun (newsvendorCost h p μ) y) = lam * K) ∧
      ∀ Qs Qb Qb1 Qb2 : ℝ,
        IsOptQty (newsvendorCost h p μ) lam K Qs →
        0 < Qb → Qb * H0fun (newsvendorCost h p μ) Qb = 2 * lam * K →
        0 < Qb1 →
        H0fun (newsvendorCost h p μ) Qb1 = Hfun (eoqCost lam L h p) (eoqQty lam K h p) →
        0 < Qb2 → (∫ y in (0 : ℝ)..Qb2, H0fun (newsvendorCost h p μ) y) = lam * K →
        eoqQty lam K h p ≤ Qs ∧ Qs ≤ Qb ∧ Qb ≤ Qb1 ∧ Qb ≤ Qb2) ∧
    ∀ Qb1 : ℝ → ℝ,
      (∀ K : ℝ, 0 < K → 0 < Qb1 K ∧
        H0fun (newsvendorCost h p μ) (Qb1 K) = Hfun (eoqCost lam L h p) (eoqQty lam K h p)) →
      MonotoneOn (fun K => Qb1 K - eoqQty lam K h p) (Set.Ioi 0) ∧
      ∃ c : ℝ, Tendsto (fun K => Qb1 K - eoqQty lam K h p) atTop (𝓝 c) := by sorry

end ZhengQR.OrderQty

