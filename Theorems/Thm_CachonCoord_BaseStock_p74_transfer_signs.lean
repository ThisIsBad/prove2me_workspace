import Mathlib
import Definitions.Def_CachonCoord_BaseStock_Model

open MeasureTheory ProbabilityTheory

namespace CachonCoord.BaseStock

/-- Cachon (2003), §6.7.1, p. 74, the paragraph after (33): signs of the transfer rates
`t_I = (1 - λ)h_r` and `t_B = β_r - λβ` over the family `λ ∈ (0, 1]`.
The inventory subsidy is nonnegative and strictly positive exactly when `λ < 1`
(the page's "t_I > 0 … valid when λ ∈ (0, 1]" fails at `λ = 1`, where `t_I = 0`);
the backorder rates fill exactly `[-β_s, β_r)`, and some contract has `t_B > 0`. -/
theorem p74_transfer_signs (M : Model) :
    (∀ lam : ℝ, 0 < lam → lam ≤ 1 → 0 ≤ M.tI lam ∧ (0 < M.tI lam ↔ lam < 1)) ∧
    M.tB '' Set.Ioc 0 1 = Set.Ico (-M.bs) M.br ∧
    ∃ lam : ℝ, 0 < lam ∧ lam ≤ 1 ∧ 0 < M.tB lam := by sorry

end CachonCoord.BaseStock

