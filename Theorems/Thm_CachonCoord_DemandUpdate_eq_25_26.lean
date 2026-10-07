import Mathlib
import Definitions.Def_CachonCoord_DemandUpdate_Model

open MeasureTheory ProbabilityTheory

namespace CachonCoord.DemandUpdate

open Model

/-- Cachon (2003), 3rd draft, §6.6.1, Eqs. (25)–(26), p. 64. Let `q2bar ξ = q_2(ξ)` solve (25),
`F(q_2(ξ)|ξ) = (p − c_2)/p`, for every signal `ξ ≥ 0`. Then
1. (25): with no inventory (`q_1 = 0`), `q ≥ 0` maximizes `Ω_2(·|0, ξ)` over `q ≥ 0` iff
   `F(q|ξ) = (p − c_2)/p`;
2. `q_2(ξ)` is (strictly) increasing in `ξ`;
3. if `ξ(q_1) = xi1` solves (26), `F(q_1|ξ(q_1)) = (p − c_2)/p`, then `q_2(ξ) > q_1` iff `ξ > ξ(q_1)`;
4. the constrained period-2 optimum over `q_2 ≥ q_1` is unique and equals `max(q_1, q_2(ξ))`;
5. the partition: if `ξ > ξ(q_1)` every optimal period-2 order is positive (`q_2 > q_1`);
   otherwise ordering nothing (`q_2 = q_1`) is optimal. -/
theorem eq_25_26 (M : Model) (q2bar : ℝ → ℝ)
    (hq2bar : ∀ ξ, 0 ≤ ξ → 0 ≤ q2bar ξ ∧ M.F ξ (q2bar ξ) = M.ratio) :
    (∀ ξ q, 0 ≤ ξ →
      ((0 ≤ q ∧ IsMaxOn (M.Omega2 0 ξ) (Set.Ici 0) q) ↔ (0 ≤ q ∧ M.F ξ q = M.ratio))) ∧
    StrictMonoOn q2bar (Set.Ici 0) ∧
    (∀ q1 xi1 ξ, 0 ≤ q1 → 0 ≤ xi1 → M.F xi1 q1 = M.ratio → 0 ≤ ξ →
      (q1 < q2bar ξ ↔ xi1 < ξ)) ∧
    (∀ q1 ξ, 0 ≤ q1 → 0 ≤ ξ →
      IsMaxOn (M.Omega2 q1 ξ) (Set.Ici q1) (max q1 (q2bar ξ)) ∧
      ∀ q, q1 ≤ q → IsMaxOn (M.Omega2 q1 ξ) (Set.Ici q1) q → q = max q1 (q2bar ξ)) ∧
    (∀ q1 xi1 ξ, 0 ≤ q1 → 0 ≤ xi1 → M.F xi1 q1 = M.ratio → 0 ≤ ξ →
      (xi1 < ξ → ∀ q, q1 ≤ q → IsMaxOn (M.Omega2 q1 ξ) (Set.Ici q1) q → q1 < q) ∧
      (ξ ≤ xi1 → IsMaxOn (M.Omega2 q1 ξ) (Set.Ici q1) q1)) := by sorry

end CachonCoord.DemandUpdate

