import Mathlib
import Definitions.Def_CachonCoord_DemandUpdate_Model
import Definitions.Def_CachonCoord_DemandUpdate_Profits

open MeasureTheory ProbabilityTheory

namespace CachonCoord.DemandUpdate

open Model

/-- Cachon (2003), 3rd draft, §6.6.1, p. 66 (the display for `Π_2(x, q_1, q_2, ξ)` and the sentence
after it). With `λ ∈ [0, 1]`, `p − b = λp` and `w_2 − b = λc_2`, the supplier's period-2 profit
after filling the retailer's order `q_2` from starting inventory `x` is
`(1 − λ)(Ω_2(q_2|q_1, ξ) − c_2 q_1) − w_2 q_1 + x c_2 − (x − q_2)⁺ c_2`, and, given `q_2 ≥ q_1`, it is
strictly increasing in `x` for `x ≤ q_1`. Hence ("the supplier surely produces and delivers the
retailer's period 1 order"), when the retailer orders the supply chain optimal `q_2(q_1, ξ)`
(selection `q2sel`) in period 2, the supplier's period-1 expected profit `Π_1(x|q_1)` is strictly
increasing in her period-1 production `x` on `[0, q_1]`. (The printed identity is off by the
constant `(1 − λ)c_2 q_1`; see the Formalization Note.) -/
theorem p66_supplier_period2 (M : Model) (lam w2 b : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hb : M.p - b = lam * M.p) (hw2 : w2 - b = lam * M.c2) :
    (∀ x q1 q2 ξ, M.supplierProfit2 w2 b x q1 q2 ξ =
      (1 - lam) * (M.Omega2 q1 ξ q2 - M.c2 * q1) - w2 * q1 + x * M.c2 - max (x - q2) 0 * M.c2) ∧
    (∀ q1 q2 ξ, q1 ≤ q2 →
      StrictMonoOn (fun x => M.supplierProfit2 w2 b x q1 q2 ξ) (Set.Iic q1)) ∧
    (∀ q2sel : ℝ → ℝ → ℝ, M.IsChainPeriod2Optimal q2sel → ∀ q1, 0 ≤ q1 →
      StrictMonoOn (M.supplierProfit1 w2 b q2sel q1) (Set.Icc 0 q1)) := by sorry

end CachonCoord.DemandUpdate

