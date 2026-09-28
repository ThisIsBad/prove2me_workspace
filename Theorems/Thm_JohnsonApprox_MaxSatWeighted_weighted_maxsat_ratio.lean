import Mathlib
import Definitions.Def_JohnsonApprox_Shared_Problem
import Definitions.Def_JohnsonApprox_MaxSatWeighted_B2

namespace JohnsonApprox.MaxSatWeighted

/-- Theorem 3 (p. 263), size-free and with the equality range corrected to `k ≥ 2`:
(1) for `k ≥ 1`, every output of B2 on an input of `MS(k)` satisfies
`S*/|SUB| ≤ 2^k/(2^k − 1)` (multiplied out); (2) for every `k ≥ 2` some input of `MS(k)` and
some choosable output attain the ratio `2^k/(2^k − 1)` exactly. At `k = 1` the ratio `2` is
never attained, so the printed "with equality" fails there. -/
theorem weighted_maxsat_ratio :
    (∀ k : ℕ, 1 ≤ k → ∀ S : Finset Shared.Clause, Shared.InMS k S → ∀ X : Finset Shared.Clause, Choosable S X →
      (2 ^ k - 1) * Shared.opt S ≤ 2 ^ k * X.card) ∧
    (∀ k : ℕ, 2 ≤ k → ∃ S : Finset Shared.Clause, Shared.InMS k S ∧ ∃ X : Finset Shared.Clause, Choosable S X ∧
      0 < X.card ∧ (2 ^ k - 1) * Shared.opt S = 2 ^ k * X.card) := by sorry

end JohnsonApprox.MaxSatWeighted

