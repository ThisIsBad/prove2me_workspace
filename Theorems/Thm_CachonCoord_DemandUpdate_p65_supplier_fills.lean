import Mathlib
import Definitions.Def_CachonCoord_DemandUpdate_Model
import Definitions.Def_CachonCoord_DemandUpdate_Profits

open MeasureTheory ProbabilityTheory

namespace CachonCoord.DemandUpdate

open Model

/-- Cachon (2003), 3rd draft, §6.6.1, p. 65 (the display defining `Π_2(y|x, q_1, q_2, ξ)` and the
sentence after it). With `λ ∈ [0, 1]`, `p − b = λp` and `w_2 = λc_2 + b`:
1. `Π_2(y|x, q_1, q_2, ξ) = (1 − λ)(Ω_2(y|q_1, ξ) − c_2 q_1) + c_2 x − w_2 q_1` for all arguments;
2. if `q_1 ≤ x < q_2` and `q_2 ≤ q_2(q_1, ξ)` (`qopt`, a maximizer of `Ω_2(·|q_1, ξ)` over `q_2 ≥ q_1`),
   then delivering in full, `y = q_2`, maximizes the supplier's profit over `x ≤ y ≤ q_2`;
3. ("i.e., the supplier does not satisfy the retailer if the retailer happens to irrationally order
   too much") if `λ < 1`, `q_1 ≤ x < q_2` and `q_2 > q_2(q_1, ξ)`, then `y = q_2` does not maximize the
   supplier's profit over `x ≤ y ≤ q_2`. -/
theorem p65_supplier_fills (M : Model) (lam w2 b : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hb : M.p - b = lam * M.p) (hw2 : w2 = lam * M.c2 + b) :
    (∀ x q1 ξ y, M.supplierProfit2Fill w2 b x q1 ξ y =
      (1 - lam) * (M.Omega2 q1 ξ y - M.c2 * q1) + M.c2 * x - w2 * q1) ∧
    (∀ q1 ξ x q2 qopt, 0 ≤ q1 → 0 ≤ ξ → q1 ≤ x → x < q2 →
      q1 ≤ qopt → IsMaxOn (M.Omega2 q1 ξ) (Set.Ici q1) qopt → q2 ≤ qopt →
      IsMaxOn (M.supplierProfit2Fill w2 b x q1 ξ) (Set.Icc x q2) q2) ∧
    (∀ q1 ξ x q2 qopt, 0 ≤ q1 → 0 ≤ ξ → q1 ≤ x → x < q2 →
      q1 ≤ qopt → IsMaxOn (M.Omega2 q1 ξ) (Set.Ici q1) qopt → lam < 1 → qopt < q2 →
      ¬ IsMaxOn (M.supplierProfit2Fill w2 b x q1 ξ) (Set.Icc x q2) q2) := by sorry

end CachonCoord.DemandUpdate

